"""."""

import logging
from typing import Any, Mapping, Optional, Union

from marshmallow import fields

from .....core.profile import ProfileSession
from .....messaging.models.base_record import BaseExchangeRecord, BaseExchangeSchema
from .....messaging.valid import UUID4_EXAMPLE
from .....storage.error import StorageDuplicateError, StorageNotFoundError
from ..messages.disclose import Disclose, DiscloseSchema
from ..messages.query import Query, QuerySchema
from . import UNENCRYPTED_TAGS

LOGGER = logging.getLogger(__name__)


class V10DiscoveryExchangeRecord(BaseExchangeRecord):
    """Represents a Discover Feature (0031) exchange record."""

    class Meta:
        """V10DiscoveryExchangeRecord metadata."""

        schema_class = "V10DiscoveryRecordSchema"

    RECORD_TYPE = "discovery_exchange_v10"
    RECORD_ID_NAME = "discovery_exchange_id"
    RECORD_TOPIC = "discover_feature"
    TAG_NAMES = {"~thread_id" if UNENCRYPTED_TAGS else "thread_id", "connection_id"}

    STATE_QUERY_SENT = "query-sent"
    STATE_DISCLOSE_RECV = "disclose-received"

    def __init__(
        self,
        *,
        state: Optional[str] = None,
        discovery_exchange_id: Optional[str] = None,
        connection_id: Optional[str] = None,
        thread_id: Optional[str] = None,
        query_msg: Union[Mapping, Query, None] = None,
        disclose: Union[Mapping, Disclose, None] = None,
        **kwargs,
    ):
        """Initialize a new V10DiscoveryExchangeRecord."""
        super().__init__(
            discovery_exchange_id, state or self.STATE_QUERY_SENT, **kwargs
        )
        self._id = discovery_exchange_id
        self.connection_id = connection_id
        self.thread_id = thread_id
        self._query_msg = Query.serde(query_msg)
        self._disclose = Disclose.serde(disclose)

    @property
    def discovery_exchange_id(self) -> str:
        """Accessor for the ID."""
        return self._id

    @property
    def query_msg(self) -> Query:
        """Accessor; get deserialized view."""
        return None if self._query_msg is None else self._query_msg.de

    @query_msg.setter
    def query_msg(self, value):
        """Setter; store de/serialized views."""
        self._query_msg = Query.serde(value)

    @property
    def disclose(self) -> Disclose:
        """Accessor; get deserialized view."""
        return None if self._disclose is None else self._disclose.de

    @disclose.setter
    def disclose(self, value):
        """Setter; store de/serialized views."""
        self._disclose = Disclose.serde(value)

    @classmethod
    async def retrieve_by_connection_id(
        cls, session: ProfileSession, connection_id: str
    ) -> "V10DiscoveryExchangeRecord":
        """Retrieve a discovery exchange record by connection."""
        tag_filter = {"connection_id": connection_id}
        return await cls.retrieve_by_tag_filter(session, tag_filter)

    @classmethod
    async def retrieve_if_exists_by_connection_id(
        cls, session: ProfileSession, connection_id: str
    ) -> Optional["V10DiscoveryExchangeRecord"]:
        """Retrieve a discovery exchange record by connection."""
        tag_filter = {"connection_id": connection_id}
        result = await cls.query(session, tag_filter)
        if len(result) > 1:
            LOGGER.warning(
                "More than one disclosure record found for connection: %s",
                connection_id,
            )

        return result[0] if result else None

    @classmethod
    async def exists_for_connection_id(
        cls, session: ProfileSession, connection_id: str
    ) -> bool:
        """Return whether a discovery exchange record exists for the given connection.

        Args:
            session (ProfileSession): session
            connection_id (str): connection_id

        Returns:
            bool: whether record exists

        """
        tag_filter = {"connection_id": connection_id}
        try:
            record = await cls.retrieve_by_tag_filter(session, tag_filter)
        except StorageNotFoundError:
            return False
        except StorageDuplicateError:
            return True
        return bool(record)

    @property
    def record_value(self) -> dict:
        """Accessor for the JSON record value generated."""
        return {
            **{
                prop: getattr(self, f"_{prop}").ser
                for prop in (
                    "query_msg",
                    "disclose",
                )
                if getattr(self, prop) is not None
            },
        }

    def __eq__(self, other: Any) -> bool:
        """Comparison between records."""
        return super().__eq__(other)


class V10DiscoveryRecordSchema(BaseExchangeSchema):
    """Schema to allow ser/deser of Discover Feature (0031) records."""

    class Meta:
        """V10DiscoveryRecordSchema metadata."""

        model_class = V10DiscoveryExchangeRecord

    discovery_exchange_id = fields.Str(
        required=False,
        metadata={
            "description": "Credential exchange identifier",
            "example": UUID4_EXAMPLE,
        },
    )
    connection_id = fields.Str(
        required=False,
        metadata={"description": "Connection identifier", "example": UUID4_EXAMPLE},
    )
    thread_id = fields.Str(
        required=False,
        metadata={"description": "Thread identifier", "example": UUID4_EXAMPLE},
    )
    query_msg = fields.Nested(
        QuerySchema(), required=False, metadata={"description": "Query message"}
    )
    disclose = fields.Nested(
        DiscloseSchema(), required=False, metadata={"description": "Disclose message"}
    )
