// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::exec::*;
use crate::kubernetes_api_objects::prelude::*;
use crate::reconciler::exec::io::*;
use crate::reconciler::spec::io::*;
use crate::reconciler::spec::reconciler as reconciler_spec;
use crate::vstd_ext::to_view::*;
use vstd::prelude::*;

verus! {

pub trait Reconciler<ReconcilerViewType, ResourceType, ReconcileStateType, ExternalAPIInput, ExternalAPIOutput, ExternalAPIType>
    where
        ResourceType: View,
        ResourceType::V: ResourceView,
        ReconcileStateType: View,
        ExternalAPIInput: ToView,
        ExternalAPIOutput: ToView,
        ReconcilerViewType: reconciler_spec::Reconciler<ResourceType::V, ReconcileStateType::V, ExternalAPIInput::V, ExternalAPIOutput::V>,
        ExternalAPIType: ExternalAPIShimLayer<ExternalAPIInput, ExternalAPIOutput>
{
    fn reconcile_init_state() -> (state: ReconcileStateType)
        ensures ReconcilerViewType::reconcile_init_state() == state@;

    fn reconcile_core(cr: &ResourceType, resp_o: Option<Response<ExternalAPIOutput>>, state: ReconcileStateType) -> (res: (ReconcileStateType, Option<Request<ExternalAPIInput>>))
        ensures ReconcilerViewType::reconcile_core(cr@, opt_response_to_view(&resp_o), state@) == (res.0@, opt_request_to_view(&res.1));

    fn reconcile_done(state: &ReconcileStateType) -> (res: bool)
        ensures ReconcilerViewType::reconcile_done(state@) == res;

    fn reconcile_error(state: &ReconcileStateType) -> (res: bool)
        ensures ReconcilerViewType::reconcile_done(state@) == res;
}

pub open spec fn resource_version_check<I, O>(prev_resp_opt: Option<ResponseView<O>>, cur_req_opt: Option<RequestView<I>>) -> bool {
    cur_req_opt.is_Some() && cur_req_opt.get_Some_0().is_k_update_request()
    ==> prev_resp_opt.is_Some() && resource_version_check_helper(prev_resp_opt.get_Some_0(), cur_req_opt.get_Some_0())
}

pub open spec fn resource_version_check_helper<I, O>(prev_resp: ResponseView<O>, cur_req: RequestView<I>) -> bool {
    let prev_get_resp = prev_resp.get_k_get_response();
    let found_obj = prev_get_resp.res.get_Ok_0();
    let cur_update_req = cur_req.get_k_update_request();
    let obj_to_update = cur_update_req.obj;
    cur_req.is_k_update_request()
    ==> prev_resp.is_k_get_response()
        && prev_get_resp.res.is_Ok()
        && found_obj.kind == obj_to_update.kind
        && found_obj.metadata.name == obj_to_update.metadata.name
        && found_obj.metadata.namespace == obj_to_update.metadata.namespace
        && found_obj.metadata.resource_version == obj_to_update.metadata.resource_version
}

}
