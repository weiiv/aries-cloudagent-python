from unittest import IsolatedAsyncioTestCase
from aries_cloudagent.tests import mock

from ....core.in_memory import InMemoryProfile

from ...base import BaseLedger
from ...multiple_ledger.base_manager import (
    BaseMultipleLedgerManager,
    MultipleLedgerManagerError,
)
from ...indy_vdr import IndyVdrLedger, IndyVdrLedgerPool

from ..ledger_requests_executor import IndyLedgerRequestsExecutor


class TestIndyLedgerRequestsExecutor(IsolatedAsyncioTestCase):
    async def asyncSetUp(self):
        self.profile = InMemoryProfile.test_profile()
        self.context = self.profile.context
        setattr(self.context, "profile", self.profile)
        self.profile.settings["ledger.ledger_config_list"] = [
            {
                "id": "test_prod_1",
                "pool_name": "test_prod_1",
                "is_production": True,
                "genesis_transactions": "genesis_transactions",
            }
        ]
        self.ledger = IndyVdrLedger(IndyVdrLedgerPool("test_prod_1"), self.profile)
        self.profile.context.injector.bind_instance(
            BaseMultipleLedgerManager,
            mock.MagicMock(
                extract_did_from_identifier=mock.MagicMock(
                    return_value="WgWxqztrNooG92RXvxSTWv"
                ),
                lookup_did_in_configured_ledgers=mock.CoroutineMock(
                    return_value=("test_prod_1", self.ledger)
                ),
                get_ledger_inst_by_id=mock.CoroutineMock(return_value=self.ledger),
            ),
        )
        self.profile.context.injector.bind_instance(BaseLedger, self.ledger)
        self.indy_ledger_requestor = IndyLedgerRequestsExecutor(self.profile)

    async def test_get_ledger_for_identifier(self):
        (
            ledger_id,
            ledger_inst,
        ) = await self.indy_ledger_requestor.get_ledger_for_identifier(
            "WgWxqztrNooG92RXvxSTWv:2:schema_name:1.0", 0
        )
        assert ledger_id == "test_prod_1"
        assert ledger_inst.pool.name == "test_prod_1"

    async def test_get_ledger_inst(self):
        ledger_inst = await self.indy_ledger_requestor.get_ledger_inst("test_prod_1")
        assert ledger_inst

    async def test_get_ledger_for_identifier_is_digit(self):
        ledger_id, ledger = await self.indy_ledger_requestor.get_ledger_for_identifier(
            "123", 0
        )
        assert ledger_id is None
        assert ledger == self.ledger

    async def test_get_ledger_for_identifier_x(self):
        self.profile.context.injector.bind_instance(
            BaseMultipleLedgerManager,
            mock.MagicMock(
                extract_did_from_identifier=mock.MagicMock(
                    return_value="WgWxqztrNooG92RXvxSTWv"
                ),
                lookup_did_in_configured_ledgers=mock.CoroutineMock(
                    side_effect=MultipleLedgerManagerError
                ),
            ),
        )
        self.indy_ledger_requestor = IndyLedgerRequestsExecutor(self.profile)
        ledger_id, ledger = await self.indy_ledger_requestor.get_ledger_for_identifier(
            "WgWxqztrNooG92RXvxSTWv:2:schema_name:1.0", 0
        )
        assert ledger_id is None
        assert ledger == self.ledger

    async def test_get_ledger_for_identifier_mult_ledger_not_set(self):
        self.profile.settings["ledger.ledger_config_list"] = None
        self.indy_ledger_requestor = IndyLedgerRequestsExecutor(self.profile)
        ledger_id, ledger = await self.indy_ledger_requestor.get_ledger_for_identifier(
            "WgWxqztrNooG92RXvxSTWv:2:schema_name:1.0", 0
        )
        assert ledger_id is None
        assert ledger == self.ledger

    async def test_get_ledger_for_identifier_mult_ledger_not_cached(self):
        (
            ledger_id,
            ledger_inst,
        ) = await self.indy_ledger_requestor.get_ledger_for_identifier(
            "GUTK6XARozQCWxqzPSUr4g", 4
        )
        assert ledger_id == "test_prod_1"
        assert ledger_inst.pool.name == "test_prod_1"
