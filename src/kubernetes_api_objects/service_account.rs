// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::api_resource::*;
use crate::kubernetes_api_objects::common::*;
use crate::kubernetes_api_objects::dynamic::*;
use crate::kubernetes_api_objects::marshal::*;
use crate::kubernetes_api_objects::object_meta::*;
use crate::kubernetes_api_objects::resource::*;
use crate::pervasive_ext::string_map::*;
use crate::pervasive_ext::string_view::*;
use vstd::prelude::*;

verus! {

/// A service account is a type of non-human account that, in Kubernetes, provides a distinct identity in a Kubernetes cluster.
/// Application Pods, system components, and entities inside and outside the cluster can use a specific ServiceAccount's credentials to identify as that ServiceAccount.
/// This identity is useful in various situations, including authenticating to the API server or implementing identity-based security policies.
///
/// This definition is a wrapper of ServiceAccount defined at
/// https://github.com/Arnavion/k8s-openapi/blob/v0.17.0/src/v1_26/api/core/v1/service_account.rs.
/// It is supposed to be used in exec controller code.
///
/// More detailed information: https://kubernetes.io/docs/concepts/security/service-accounts/.

#[verifier(external_body)]
pub struct ServiceAccount {
    inner: deps_hack::k8s_openapi::api::core::v1::ServiceAccount,
}

impl ServiceAccount {
    pub spec fn view(&self) -> ServiceAccountView;

    #[verifier(external_body)]
    pub fn default() -> (service_account: ServiceAccount)
        ensures
            service_account@ == ServiceAccountView::default(),
    {
        ServiceAccount {
            inner: deps_hack::k8s_openapi::api::core::v1::ServiceAccount::default(),
        }
    }

    #[verifier(external_body)]
    pub fn metadata(&self) -> (metadata: ObjectMeta)
        ensures
            metadata@ == self@.metadata,
    {
        todo!()
    }

    #[verifier(external_body)]
    pub fn set_metadata(&mut self, metadata: ObjectMeta)
        ensures
            self@ == old(self)@.set_metadata(metadata@),
    {
        self.inner.metadata = metadata.into_kube();
    }

    #[verifier(external)]
    pub fn from_kube(inner: deps_hack::k8s_openapi::api::core::v1::ServiceAccount) -> ServiceAccount {
        ServiceAccount {
            inner: inner
        }
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::ServiceAccount {
        self.inner
    }

    #[verifier(external_body)]
    pub fn api_resource() -> (res: ApiResource)
        ensures
            res@.kind == Kind::ServiceAccountKind,
    {
        ApiResource::from_kube(deps_hack::kube::api::ApiResource::erase::<deps_hack::k8s_openapi::api::core::v1::ServiceAccount>(&()))
    }

    #[verifier(external_body)]
    pub fn to_dynamic_object(self) -> (obj: DynamicObject)
        ensures
            obj@ == self@.to_dynamic_object(),
    {
        DynamicObject::from_kube(
            deps_hack::k8s_openapi::serde_json::from_str(&deps_hack::k8s_openapi::serde_json::to_string(&self.inner).unwrap()).unwrap()
        )
    }

    #[verifier(external_body)]
    pub fn from_dynamic_object(obj: DynamicObject) -> (cm: ServiceAccount)
        ensures
            cm@ == ServiceAccountView::from_dynamic_object(obj@),
    {
        ServiceAccount {inner: obj.into_kube().try_parse::<deps_hack::k8s_openapi::api::core::v1::ServiceAccount>().unwrap()}
    }
}

/// ServiceAccountView is the ghost type of ServiceAccount.
/// It is supposed to be used in spec and proof code.

pub struct ServiceAccountView {
    pub metadata: ObjectMetaView,
}

impl ServiceAccountView {
    pub open spec fn default() -> ServiceAccountView {
        ServiceAccountView {
            metadata: ObjectMetaView::default(),
        }
    }

    pub open spec fn set_metadata(self, metadata: ObjectMetaView) -> ServiceAccountView {
        ServiceAccountView {
            metadata: metadata,
            ..self
        }
    }

}

impl ResourceView for ServiceAccountView {
    open spec fn metadata(self) -> ObjectMetaView {
        self.metadata
    }

    open spec fn kind(self) -> Kind {
        Kind::ServiceAccountKind
    }

    open spec fn object_ref(self) -> ObjectRef {
        ObjectRef {
            kind: self.kind(),
            name: self.metadata.name.get_Some_0(),
            namespace: self.metadata.namespace.get_Some_0(),
        }
    }

    open spec fn to_dynamic_object(self) -> DynamicObjectView {
        DynamicObjectView {
            kind: self.kind(),
            metadata: self.metadata,
            data: Value::Null,
        }
    }

    open spec fn from_dynamic_object(obj: DynamicObjectView) -> ServiceAccountView {
        ServiceAccountView {
            metadata: obj.metadata,
        }
    }

    proof fn to_dynamic_preserves_integrity() {}
}

}