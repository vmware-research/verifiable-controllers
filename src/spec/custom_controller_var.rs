// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT

#[allow(unused_imports)]
use crate::apis::*;
#[allow(unused_imports)]
use crate::common::*;
#[allow(unused_imports)]
use builtin::equal;
#[allow(unused_imports)]
use builtin_macros::*;

#[derive(Structural, PartialEq, Eq)]
pub enum CustomReconcileStep {
    CheckIfCMGExists,
    CheckIfCMExists,
    CreateCM1,
    CreateCM2,
}

#[derive(PartialEq, Eq)]
pub struct ConfigMapGeneratorL {
    pub metadata: MetadataL,
}

verus! {

impl ConfigMapGeneratorL {
    pub open spec fn key(&self) -> ObjectKey {
        ObjectKey{
            object_type: StringL::ConfigMapGenerator,
            namespace: self.metadata.namespace,
            name: self.metadata.name,
        }
    }

    pub open spec fn matches(&self, key:ObjectKey) -> bool {
        equal(self.key(), key)
    }
}

#[derive(PartialEq, Eq)]
pub enum CustomResourceObject {
    ConfigMapGenerator(ConfigMapGeneratorL),
}

impl CustomResourceObject {
    pub open spec fn matches(&self, key:ObjectKey) -> bool {
        match *self {
            CustomResourceObject::ConfigMapGenerator(cmg) => cmg.matches(key),
        }
    }
}

}
