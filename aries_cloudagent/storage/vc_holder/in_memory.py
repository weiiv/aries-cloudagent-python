"""Basic in-memory storage implementation of VC holder interface."""

from typing import Mapping, Optional, Sequence

from dateutil.parser import ParserError
from dateutil.parser import parse as dateutil_parser

from ...core.in_memory import InMemoryProfile
from ..in_memory import InMemoryStorage, InMemoryStorageSearch
from .base import VCHolder, VCRecordSearch
from .vc_record import VCRecord
from .xform import VC_CRED_RECORD_TYPE, storage_to_vc_record, vc_to_storage_record


class InMemoryVCHolder(VCHolder):
    """Basic in-memory storage class."""

    def __init__(self, profile: InMemoryProfile):
        """Initialize the in-memory VC holder instance."""
        self._profile = profile
        self._store = InMemoryStorage(profile)

    def build_type_or_schema_query(self, uri_list: Sequence[str]) -> dict:
        """Build and return in-memory backend specific type_or_schema_query."""
        type_or_schema_query = {"$and": []}
        for uri in uri_list:
            tag_or_list = []
            tag_or_list.append({f"type:{uri}": "1"})
            tag_or_list.append({f"schm:{uri}": "1"})
            type_or_schema_query["$and"].append({"$or": tag_or_list})
        return type_or_schema_query

    async def store_credential(self, cred: VCRecord):
        """Add a new VC record to the store.

        Args:
            cred: The VCRecord instance to store
        Raises:
            StorageDuplicateError: If the record_id is not unique

        """
        record = vc_to_storage_record(cred)
        await self._store.add_record(record)

    async def retrieve_credential_by_id(self, record_id: str) -> VCRecord:
        """Fetch a VC record by its record ID.

        Raises:
            StorageNotFoundError: If the record is not found

        """
        record = await self._store.get_record(VC_CRED_RECORD_TYPE, record_id)
        return storage_to_vc_record(record)

    async def retrieve_credential_by_given_id(self, given_id: str) -> VCRecord:
        """Fetch a VC record by its given ID ('id' property).

        Raises:
            StorageNotFoundError: If the record is not found

        """
        record = await self._store.find_record(
            VC_CRED_RECORD_TYPE, {"given_id": given_id}
        )
        return storage_to_vc_record(record)

    async def delete_credential(self, cred: VCRecord):
        """Remove a previously-stored VC record.

        Raises:
            StorageNotFoundError: If the record is not found

        """
        await self._store.delete_record(vc_to_storage_record(cred))

    def search_credentials(
        self,
        contexts: Sequence[str] = None,
        types: Sequence[str] = None,
        schema_ids: Optional[str] = None,
        issuer_id: Optional[str] = None,
        subject_ids: Optional[str] = None,
        proof_types: Sequence[str] = None,
        given_id: Optional[str] = None,
        tag_query: Optional[Mapping] = None,
        pd_uri_list: Sequence[str] = None,
    ) -> "VCRecordSearch":
        """Start a new VC record search.

        Args:
            contexts (Sequence[str], optional): An inclusive list of JSON-LD contexts
                to match.
            types (Sequence[str], optional): An inclusive list of JSON-LD types to
                match.
            schema_ids (str, optional): An inclusive list of credential schema
                identifiers.
            issuer_id (str, optional): The ID of the credential issuer.
            subject_ids (str, optional): The IDs of credential subjects all of which
                to match.
            proof_types (Sequence[str], optional): The signature suite types used for
                the proof objects.
            given_id (str, optional): The given id of the credential.
            tag_query (Mapping, optional): A tag filter clause.
            pd_uri_list (Sequence[str], optional): A list of presentation definition
                URIs.

        Returns:
            VCRecordSearch: An instance of VCRecordSearch representing the search
                query.

        """
        query = {}
        if contexts:
            for ctx_val in contexts:
                query[f"ctxt:{ctx_val}"] = "1"
        if types:
            for type_val in types:
                query[f"type:{type_val}"] = "1"
        if schema_ids:
            for schema_val in schema_ids:
                query[f"schm:{schema_val}"] = "1"
        if subject_ids:
            for subject_id in subject_ids:
                query[f"subj:{subject_id}"] = "1"
        if proof_types:
            for proof_type in proof_types:
                query[f"ptyp:{proof_type}"] = "1"
        if issuer_id:
            query["issuer_id"] = issuer_id
        if given_id:
            query["given_id"] = given_id
        if tag_query:
            query.update(tag_query)
        if pd_uri_list:
            query.update(self.build_type_or_schema_query(pd_uri_list))
        search = self._store.search_records(VC_CRED_RECORD_TYPE, query)
        return InMemoryVCRecordSearch(search)


class InMemoryVCRecordSearch(VCRecordSearch):
    """In-memory search for VC records."""

    def __init__(self, search: InMemoryStorageSearch):
        """Initialize the in-memory VC record search."""
        self._search = search

    async def fetch(self, max_count: Optional[int] = None) -> Sequence[VCRecord]:
        """Fetch the next list of VC records from the store.

        Args:
            max_count: Max number of records to return. If not provided,
              defaults to the backend's preferred page size

        Returns:
            A list of `VCRecord` instances

        """
        rows = await self._search.fetch(max_count)
        records = [storage_to_vc_record(r) for r in rows]
        try:
            records.sort(
                key=lambda v: dateutil_parser(v.cred_value.get("issuanceDate")),
                reverse=True,
            )
            return records
        except ParserError:
            return records
