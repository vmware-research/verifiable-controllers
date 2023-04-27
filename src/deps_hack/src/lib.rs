pub use anyhow;
pub use futures;
pub use k8s_openapi;
pub use kube;
pub use schemars;
pub use serde;
pub use serde_json;
pub use serde_yaml;
pub use thiserror;
pub use tokio;
pub use tracing;

#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("MissingObjectKey: {0}")]
    MissingObjectKey(&'static str),
}

#[derive(
    kube::CustomResource, Debug, Clone, serde::Deserialize, serde::Serialize, schemars::JsonSchema,
)]
#[kube(group = "anvil.dev", version = "v1", kind = "SimpleCR")]
#[kube(shortname = "cr", namespaced)]
pub struct SimpleCRSpec {
    pub content: String,
}
