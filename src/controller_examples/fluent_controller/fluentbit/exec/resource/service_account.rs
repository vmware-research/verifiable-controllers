// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use super::common::*;
use crate::external_api::exec::*;
use crate::fluent_controller::fluentbit::common::*;
use crate::fluent_controller::fluentbit::exec::resource::role::RoleBuilder;
use crate::fluent_controller::fluentbit::exec::types::*;
use crate::fluent_controller::fluentbit::spec::resource as spec_resource;
use crate::fluent_controller::fluentbit::spec::types::FluentBitView;
use crate::kubernetes_api_objects::resource::ResourceWrapper;
use crate::kubernetes_api_objects::{
    container::*, label_selector::*, pod_template_spec::*, prelude::*, resource_requirements::*,
    volume::*,
};
use crate::reconciler::exec::{io::*, reconciler::*, resource_builder::*};
use crate::vstd_ext::string_map::StringMap;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::string::*;

verus! {

pub struct ServiceAccountBuilder {}

impl ResourceBuilder<FluentBit, FluentBitReconcileState, spec_resource::ServiceAccountBuilder> for ServiceAccountBuilder {
    open spec fn requirements(fb: FluentBitView) -> bool {
        &&& fb.well_formed()
    }

    fn get_request(fb: &FluentBit) -> KubeGetRequest {
        KubeGetRequest {
            api_resource: ServiceAccount::api_resource(),
            name: make_service_account_name(fb),
            namespace: fb.metadata().namespace().unwrap(),
        }
    }

    fn make(fb: &FluentBit, state: &FluentBitReconcileState) -> Result<DynamicObject, ()> {
        Ok(make_service_account(fb).marshal())
    }

    fn update(fb: &FluentBit, state: &FluentBitReconcileState, obj: DynamicObject) -> Result<DynamicObject, ()> {
        let sa = ServiceAccount::unmarshal(obj);
        if sa.is_ok() {
            Ok(update_service_account(fb, sa.unwrap()).marshal())
        } else {
            Err(())
        }
    }

    fn state_after_create_or_update(obj: DynamicObject, state: FluentBitReconcileState) -> (res: Result<FluentBitReconcileState, ()>) {
        let sa = ServiceAccount::unmarshal(obj);
        if sa.is_ok() {
            Ok(state)
        } else {
            Err(())
        }
    }
}

pub fn update_service_account(fb: &FluentBit, found_service_account: ServiceAccount) -> (service_account: ServiceAccount)
    requires
        fb@.well_formed(),
    ensures
        service_account@ == spec_resource::update_service_account(fb@, found_service_account@),
{
    let mut service_account = found_service_account.clone();
    let made_service_account = make_service_account(fb);
    service_account.set_metadata({
        let mut metadata = found_service_account.metadata();
        metadata.set_owner_references(make_owner_references(fb));
        metadata.unset_finalizers();
        metadata.set_labels(made_service_account.metadata().labels().unwrap());
        metadata.set_annotations(made_service_account.metadata().annotations().unwrap());
        metadata
    });
    service_account
}

pub fn make_service_account_name(fb: &FluentBit) -> (name: String)
    requires
        fb@.well_formed(),
    ensures
        name@ == spec_resource::make_service_account_name(fb@),
{
    fb.metadata().name().unwrap()
}

pub fn make_service_account(fb: &FluentBit) -> (service_account: ServiceAccount)
    requires
        fb@.well_formed(),
    ensures
        service_account@ == spec_resource::make_service_account(fb@),
{
    let mut service_account = ServiceAccount::default();
    service_account.set_metadata({
        let mut metadata = ObjectMeta::default();
        metadata.set_name(make_service_account_name(fb));
        metadata.set_owner_references(make_owner_references(fb));
        metadata.set_labels(make_labels(fb));
        metadata.set_annotations(fb.spec().annotations());
        metadata
    });
    service_account
}

}
