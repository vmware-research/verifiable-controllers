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
use deps_hack::k8s_openapi::ByteString;
use vstd::prelude::*;

verus! {

/// Secret is a type of API object used to store confidential data in key-value pairs.
/// A Secret object can be used to set environment variables or configuration files
/// in a Volume mounted to a Pod.
///
/// This definition is a wrapper of Secret defined at
/// https://github.com/Arnavion/k8s-openapi/blob/v0.17.0/src/v1_26/api/core/v1/secret.rs.
/// It is supposed to be used in exec controller code.
///
/// More detailed information: https://kubernetes.io/docs/concepts/configuration/secret/.

#[verifier(external_body)]
pub struct Secret {
    inner: deps_hack::k8s_openapi::api::core::v1::Secret,
}

impl Secret {
    pub spec fn view(&self) -> SecretView;

    #[verifier(external_body)]
    pub fn default() -> (secret: Secret)
        ensures
            secret@ == SecretView::default(),
    {
        Secret {
            inner: deps_hack::k8s_openapi::api::core::v1::Secret::default(),
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
    pub fn data(&self) -> (data: Option<StringMap>)
        ensures
            self@.data.is_Some() == data.is_Some(),
            data.is_Some() ==> data.get_Some_0()@ == self@.data.get_Some_0(),
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

    #[verifier(external_body)]
    pub fn set_data(&mut self, data: StringMap)
        ensures
            self@ == old(self)@.set_data(data@),
    {
        let string_map = data.into_rust_map();
        let mut binary_map: std::collections::BTreeMap<std::string::String, ByteString> = std::collections::BTreeMap::new();
        for (key, value) in string_map {
            binary_map.insert(key, ByteString(value.into_bytes()));
        }
        self.inner.data = std::option::Option::Some(binary_map) // TODO: convert StringMap to String:ByteString map
    }

    #[verifier(external_body)]
    pub fn set_type(&mut self, type_: String)
        ensures
            self@ == old(self)@.set_type(type_@),
    {
        self.inner.type_ = std::option::Option::Some(type_.into_rust_string())
    }

    #[verifier(external)]
    pub fn from_kube(inner: deps_hack::k8s_openapi::api::core::v1::Secret) -> Secret {
        Secret {
            inner: inner
        }
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::Secret {
        self.inner
    }

    #[verifier(external_body)]
    pub fn api_resource() -> (res: ApiResource)
        ensures
            res@.kind == Kind::SecretKind,
    {
        ApiResource::from_kube(deps_hack::kube::api::ApiResource::erase::<deps_hack::k8s_openapi::api::core::v1::Secret>(&()))
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
    pub fn from_dynamic_object(obj: DynamicObject) -> (cm: Secret)
        ensures
            cm@ == SecretView::from_dynamic_object(obj@),
    {
        Secret {inner: obj.into_kube().try_parse::<deps_hack::k8s_openapi::api::core::v1::Secret>().unwrap()}
    }
}

/// SecretView is the ghost type of Secret.
/// It is supposed to be used in spec and proof code.

pub struct SecretView {
    pub metadata: ObjectMetaView,
    pub data: Option<Map<StringView, StringView>>, // For view, String:String map is used instead of String:Bytestring map.
    pub type_: Option<StringView>,
}

impl SecretView {
    pub open spec fn default() -> SecretView {
        SecretView {
            metadata: ObjectMetaView::default(),
            data: Option::None,
            type_: Option::None,
        }
    }

    pub open spec fn set_metadata(self, metadata: ObjectMetaView) -> SecretView {
        SecretView {
            metadata: metadata,
            ..self
        }
    }

    pub open spec fn set_data(self, data: Map<StringView, StringView>) -> SecretView {
        SecretView {
            data: Option::Some(data),
            ..self
        }
    }

    pub open spec fn set_type(self, type_: StringView) -> SecretView {
        SecretView {
            type_: Option::Some(type_),
            ..self
        }
    }

    pub open spec fn data_field() -> nat {0}

    pub open spec fn type_field() -> nat {1}
}

impl ResourceView for SecretView {
    open spec fn metadata(self) -> ObjectMetaView {
        self.metadata
    }

    open spec fn kind(self) -> Kind {
        Kind::SecretKind
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
            data: Value::Object(
                Map::empty()
                .insert(Self::data_field(),
                        if self.data.is_None() { Value::Null } else {
                            Value::StringStringMap(self.data.get_Some_0())
                        }
                ).insert(Self::type_field(),
                         if self.type_.is_None() { Value::Null } else {
                             Value::String(self.type_.get_Some_0())
                         }
                )
            ),
        }
    }

    open spec fn from_dynamic_object(obj: DynamicObjectView) -> SecretView {
        SecretView {
            metadata: obj.metadata,
            data: if obj.data.get_Object_0()[Self::data_field()].is_Null() { Option::None } else {
                Option::Some(obj.data.get_Object_0()[Self::data_field()].get_StringStringMap_0())
            },
            type_: if obj.data.get_Object_0()[Self::type_field()].is_Null() { Option::None } else {
                Option::Some(obj.data.get_Object_0()[Self::type_field()].get_String_0())
            },
        }
    }

    proof fn to_dynamic_preserves_integrity() {}
}

}