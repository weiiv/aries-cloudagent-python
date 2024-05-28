from unittest import IsolatedAsyncioTestCase

from aries_cloudagent.tests import mock

from .....admin.request_context import AdminRequestContext
from .....core.in_memory import InMemoryProfile
from .....storage.error import StorageNotFoundError
from .. import routes as test_module


class TestActionMenuRoutes(IsolatedAsyncioTestCase):
    def setUp(self):
        self.session_inject = {}
        profile = InMemoryProfile.test_profile(
            settings={
                "admin.admin_api_key": "secret-key",
            }
        )
        self.context = AdminRequestContext.test_context(self.session_inject, profile)
        self.request_dict = {
            "context": self.context,
            "outbound_message_router": mock.CoroutineMock(),
        }
        self.request = mock.MagicMock(
            app={},
            match_info={},
            query={},
            __getitem__=lambda _, k: self.request_dict[k],
            headers={"x-api-key": "secret-key"},
        )

    async def test_actionmenu_close(self):
        self.request.json = mock.CoroutineMock()
        self.request.match_info = {"conn_id": "dummy"}

        test_module.retrieve_connection_menu = mock.CoroutineMock()
        test_module.save_connection_menu = mock.CoroutineMock()

        with mock.patch.object(test_module.web, "json_response") as mock_response:
            res = await test_module.actionmenu_close(self.request)
            mock_response.assert_called_once_with({})

    async def test_actionmenu_close_x(self):
        self.request.json = mock.CoroutineMock()
        self.request.match_info = {"conn_id": "dummy"}

        test_module.retrieve_connection_menu = mock.CoroutineMock()
        test_module.save_connection_menu = mock.CoroutineMock(
            side_effect=test_module.StorageError()
        )

        with self.assertRaises(test_module.web.HTTPBadRequest):
            await test_module.actionmenu_close(self.request)

    async def test_actionmenu_close_not_found(self):
        self.request.json = mock.CoroutineMock()
        self.request.match_info = {"conn_id": "dummy"}

        test_module.retrieve_connection_menu = mock.CoroutineMock(return_value=None)
        with self.assertRaises(test_module.web.HTTPNotFound):
            await test_module.actionmenu_close(self.request)

    async def test_actionmenu_fetch(self):
        self.request.json = mock.CoroutineMock()
        self.request.match_info = {"conn_id": "dummy"}

        test_module.retrieve_connection_menu = mock.CoroutineMock(return_value=None)

        with mock.patch.object(test_module.web, "json_response") as mock_response:
            res = await test_module.actionmenu_fetch(self.request)
            mock_response.assert_called_once_with({"result": None})

    async def test_actionmenu_perform(self):
        self.request.json = mock.CoroutineMock()
        self.request.match_info = {"conn_id": "dummy"}

        with mock.patch.object(
            test_module, "ConnRecord", autospec=True
        ) as mock_conn_record, mock.patch.object(
            test_module, "Perform", autospec=True
        ) as mock_perform, mock.patch.object(
            test_module.web, "json_response"
        ) as mock_response:
            mock_conn_record.retrieve_by_id = mock.CoroutineMock()

            res = await test_module.actionmenu_perform(self.request)
            mock_response.assert_called_once_with({})
            self.request["outbound_message_router"].assert_called_once_with(
                mock_perform.return_value,
                connection_id=self.request.match_info["conn_id"],
            )

    async def test_actionmenu_perform_no_conn_record(self):
        self.request.json = mock.CoroutineMock()
        self.request.match_info = {"conn_id": "dummy"}

        with mock.patch.object(
            test_module, "ConnRecord", autospec=True
        ) as mock_conn_record, mock.patch.object(
            test_module, "Perform", autospec=True
        ) as mock_perform:
            # Emulate storage not found (bad connection id)
            mock_conn_record.retrieve_by_id = mock.CoroutineMock(
                side_effect=StorageNotFoundError
            )

            with self.assertRaises(test_module.web.HTTPNotFound):
                await test_module.actionmenu_perform(self.request)

    async def test_actionmenu_perform_conn_not_ready(self):
        self.request.json = mock.CoroutineMock()
        self.request.match_info = {"conn_id": "dummy"}

        with mock.patch.object(
            test_module, "ConnRecord", autospec=True
        ) as mock_conn_record, mock.patch.object(
            test_module, "Perform", autospec=True
        ) as mock_perform:
            # Emulate connection not ready
            mock_conn_record.retrieve_by_id = mock.CoroutineMock()
            mock_conn_record.retrieve_by_id.return_value.is_ready = False

            with self.assertRaises(test_module.web.HTTPForbidden):
                await test_module.actionmenu_perform(self.request)

    async def test_actionmenu_request(self):
        self.request.json = mock.CoroutineMock()
        self.request.match_info = {"conn_id": "dummy"}

        with mock.patch.object(
            test_module, "ConnRecord", autospec=True
        ) as mock_conn_record, mock.patch.object(
            test_module, "MenuRequest", autospec=True
        ) as menu_request, mock.patch.object(
            test_module.web, "json_response"
        ) as mock_response:
            mock_conn_record.retrieve_by_id = mock.CoroutineMock()

            res = await test_module.actionmenu_request(self.request)
            mock_response.assert_called_once_with({})
            self.request["outbound_message_router"].assert_called_once_with(
                menu_request.return_value,
                connection_id=self.request.match_info["conn_id"],
            )

    async def test_actionmenu_request_no_conn_record(self):
        self.request.json = mock.CoroutineMock()
        self.request.match_info = {"conn_id": "dummy"}

        with mock.patch.object(
            test_module, "ConnRecord", autospec=True
        ) as mock_conn_record, mock.patch.object(
            test_module, "Perform", autospec=True
        ) as mock_perform:
            # Emulate storage not found (bad connection id)
            mock_conn_record.retrieve_by_id = mock.CoroutineMock(
                side_effect=StorageNotFoundError
            )

            with self.assertRaises(test_module.web.HTTPNotFound):
                await test_module.actionmenu_request(self.request)

    async def test_actionmenu_request_conn_not_ready(self):
        self.request.json = mock.CoroutineMock()
        self.request.match_info = {"conn_id": "dummy"}

        with mock.patch.object(
            test_module, "ConnRecord", autospec=True
        ) as mock_conn_record, mock.patch.object(
            test_module, "Perform", autospec=True
        ) as mock_perform:
            # Emulate connection not ready
            mock_conn_record.retrieve_by_id = mock.CoroutineMock()
            mock_conn_record.retrieve_by_id.return_value.is_ready = False

            with self.assertRaises(test_module.web.HTTPForbidden):
                await test_module.actionmenu_request(self.request)

    async def test_actionmenu_send(self):
        self.request.json = mock.CoroutineMock()
        self.request.match_info = {"conn_id": "dummy"}

        with mock.patch.object(
            test_module, "ConnRecord", autospec=True
        ) as mock_conn_record, mock.patch.object(
            test_module, "Menu", autospec=True
        ) as mock_menu, mock.patch.object(
            test_module.web, "json_response"
        ) as mock_response:
            mock_conn_record.retrieve_by_id = mock.CoroutineMock()
            mock_menu.deserialize = mock.MagicMock()

            res = await test_module.actionmenu_send(self.request)
            mock_response.assert_called_once_with({})
            self.request["outbound_message_router"].assert_called_once_with(
                mock_menu.deserialize.return_value,
                connection_id=self.request.match_info["conn_id"],
            )

    async def test_actionmenu_send_deserialize_x(self):
        self.request.json = mock.CoroutineMock()
        self.request.match_info = {"conn_id": "dummy"}

        with mock.patch.object(
            test_module, "ConnRecord", autospec=True
        ) as mock_conn_record, mock.patch.object(
            test_module, "Menu", autospec=True
        ) as mock_menu:
            mock_conn_record.retrieve_by_id = mock.CoroutineMock()
            mock_menu.deserialize = mock.MagicMock(
                side_effect=test_module.BaseModelError("cannot deserialize")
            )

            with self.assertRaises(test_module.web.HTTPBadRequest):
                await test_module.actionmenu_send(self.request)

    async def test_actionmenu_send_no_conn_record(self):
        self.request.json = mock.CoroutineMock()
        self.request.match_info = {"conn_id": "dummy"}

        with mock.patch.object(
            test_module, "ConnRecord", autospec=True
        ) as mock_conn_record, mock.patch.object(
            test_module, "Menu", autospec=True
        ) as mock_menu:
            mock_menu.deserialize = mock.MagicMock()

            # Emulate storage not found (bad connection id)
            mock_conn_record.retrieve_by_id = mock.CoroutineMock(
                side_effect=StorageNotFoundError
            )

            with self.assertRaises(test_module.web.HTTPNotFound):
                await test_module.actionmenu_send(self.request)

    async def test_actionmenu_send_conn_not_ready(self):
        self.request.json = mock.CoroutineMock()
        self.request.match_info = {"conn_id": "dummy"}

        with mock.patch.object(
            test_module, "ConnRecord", autospec=True
        ) as mock_conn_record, mock.patch.object(
            test_module, "Menu", autospec=True
        ) as mock_menu:
            mock_menu.deserialize = mock.MagicMock()

            # Emulate connection not ready
            mock_conn_record.retrieve_by_id = mock.CoroutineMock()
            mock_conn_record.retrieve_by_id.return_value.is_ready = False

            with self.assertRaises(test_module.web.HTTPForbidden):
                await test_module.actionmenu_send(self.request)

    async def test_register(self):
        mock_app = mock.MagicMock()
        mock_app.add_routes = mock.MagicMock()

        await test_module.register(mock_app)
        mock_app.add_routes.assert_called_once()

    async def test_post_process_routes(self):
        mock_app = mock.MagicMock(_state={"swagger_dict": {}})
        test_module.post_process_routes(mock_app)
        assert "tags" in mock_app._state["swagger_dict"]
