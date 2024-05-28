"""Classes for configuring the default injection context."""

from ..anoncreds.registry import AnonCredsRegistry
from ..cache.base import BaseCache
from ..cache.in_memory import InMemoryCache
from ..core.event_bus import EventBus
from ..core.goal_code_registry import GoalCodeRegistry
from ..core.plugin_registry import PluginRegistry
from ..core.profile import ProfileManager, ProfileManagerProvider
from ..core.protocol_registry import ProtocolRegistry
from ..protocols.actionmenu.v1_0.base_service import BaseMenuService
from ..protocols.actionmenu.v1_0.driver_service import DriverMenuService
from ..protocols.introduction.v0_1.base_service import BaseIntroductionService
from ..protocols.introduction.v0_1.demo_service import DemoIntroductionService
from ..resolver.did_resolver import DIDResolver
from ..tails.base import BaseTailsServer
from ..transport.wire_format import BaseWireFormat
from ..utils.stats import Collector
from ..wallet.default_verification_key_strategy import (
    BaseVerificationKeyStrategy,
    DefaultVerificationKeyStrategy,
)
from ..wallet.did_method import DIDMethods
from ..wallet.key_type import KeyTypes
from .base_context import ContextBuilder
from .injection_context import InjectionContext
from .provider import CachedProvider, ClassProvider


class DefaultContextBuilder(ContextBuilder):
    """Default context builder."""

    async def build_context(self) -> InjectionContext:
        """Build the base injection context; set DIDComm prefix to emit."""
        context = InjectionContext(settings=self.settings)
        context.settings.set_default("default_label", "Aries Cloud Agent")

        if context.settings.get("timing.enabled"):
            timing_log = context.settings.get("timing.log_file")
            collector = Collector(log_path=timing_log)
            context.injector.bind_instance(Collector, collector)

        # Shared in-memory cache
        context.injector.bind_instance(BaseCache, InMemoryCache())

        # Global protocol registry
        context.injector.bind_instance(ProtocolRegistry, ProtocolRegistry())

        # Global goal code registry
        context.injector.bind_instance(GoalCodeRegistry, GoalCodeRegistry())

        # Global event bus
        context.injector.bind_instance(EventBus, EventBus())

        # Global did resolver
        context.injector.bind_instance(DIDResolver, DIDResolver([]))
        context.injector.bind_instance(AnonCredsRegistry, AnonCredsRegistry())
        context.injector.bind_instance(DIDMethods, DIDMethods())
        context.injector.bind_instance(KeyTypes, KeyTypes())
        context.injector.bind_instance(
            BaseVerificationKeyStrategy, DefaultVerificationKeyStrategy()
        )

        await self.bind_providers(context)
        await self.load_plugins(context)

        return context

    async def bind_providers(self, context: InjectionContext):
        """Bind various class providers."""

        context.injector.bind_provider(ProfileManager, ProfileManagerProvider())

        wallet_type = self.settings.get("wallet.type")
        if wallet_type == "askar-anoncreds":
            context.injector.bind_provider(
                BaseTailsServer,
                ClassProvider(
                    "aries_cloudagent.tails.anoncreds_tails_server.AnonCredsTailsServer",
                ),
            )
        else:
            context.injector.bind_provider(
                BaseTailsServer,
                ClassProvider(
                    "aries_cloudagent.tails.indy_tails_server.IndyTailsServer",
                ),
            )

        # Register default pack format
        context.injector.bind_provider(
            BaseWireFormat,
            CachedProvider(
                # StatsProvider(
                ClassProvider("aries_cloudagent.transport.pack_format.PackWireFormat"),
                #    (
                #        "encode_message", "parse_message"
                #    ),
                # )
            ),
        )

        # Allow action menu to be provided by driver
        context.injector.bind_instance(BaseMenuService, DriverMenuService(context))
        context.injector.bind_instance(
            BaseIntroductionService, DemoIntroductionService()
        )

    async def load_plugins(self, context: InjectionContext):
        """Set up plugin registry and load plugins."""

        plugin_registry = PluginRegistry(
            blocklist=self.settings.get("blocked_plugins", [])
        )
        wallet_type = self.settings.get("wallet.type")
        context.injector.bind_instance(PluginRegistry, plugin_registry)

        # Register standard protocol plugins
        plugin_registry.register_package("aries_cloudagent.protocols")

        # Currently providing admin routes only
        plugin_registry.register_plugin("aries_cloudagent.holder")
        plugin_registry.register_plugin("aries_cloudagent.ledger")
        plugin_registry.register_plugin("aries_cloudagent.messaging.jsonld")
        plugin_registry.register_plugin("aries_cloudagent.resolver")
        plugin_registry.register_plugin("aries_cloudagent.settings")
        plugin_registry.register_plugin("aries_cloudagent.vc")
        plugin_registry.register_plugin("aries_cloudagent.wallet")

        anoncreds_plugins = [
            "aries_cloudagent.anoncreds",
            "aries_cloudagent.anoncreds.default.did_indy",
            "aries_cloudagent.anoncreds.default.did_web",
            "aries_cloudagent.anoncreds.default.legacy_indy",
            "aries_cloudagent.revocation_anoncreds",
        ]

        askar_plugins = [
            "aries_cloudagent.messaging.credential_definitions",
            "aries_cloudagent.messaging.schemas",
            "aries_cloudagent.revocation",
        ]

        def register_askar_plugins():
            for plugin in askar_plugins:
                plugin_registry.register_plugin(plugin)

        def register_anoncreds_plugins():
            for plugin in anoncreds_plugins:
                plugin_registry.register_plugin(plugin)

        if wallet_type == "askar-anoncreds":
            register_anoncreds_plugins()
        else:
            register_askar_plugins()

        if context.settings.get("multitenant.admin_enabled"):
            plugin_registry.register_plugin("aries_cloudagent.multitenant.admin")
            register_askar_plugins()
            register_anoncreds_plugins()

        # Register external plugins
        for plugin_path in self.settings.get("external_plugins", []):
            plugin_registry.register_plugin(plugin_path)

        # Register message protocols
        await plugin_registry.init_context(context)
