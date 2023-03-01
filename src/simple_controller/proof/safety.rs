// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_cluster::spec::{
    common::*,
    controller::common::{controller_req_msg, ControllerAction, ControllerActionInput},
    distributed_system::*,
};
use crate::pervasive::{option::*, result::*};
use crate::simple_controller::spec::{
    simple_reconciler,
    simple_reconciler::{simple_reconciler, SimpleReconcileState},
};
use crate::temporal_logic::{defs::*, rules::*};
use builtin::*;
use builtin_macros::*;

verus! {

pub proof fn lemma_always_reconcile_init_implies_no_pending_req(cr_key: ResourceKey)
    ensures
        sm_spec(simple_reconciler()).entails(always(
            lift_state(|s: State<SimpleReconcileState>| {
                &&& s.reconcile_state_contains(cr_key)
                &&& s.reconcile_state_of(cr_key).local_state.reconcile_pc === simple_reconciler::init_pc()
            })
                .implies(lift_state(|s: State<SimpleReconcileState>| {
                    &&& s.reconcile_state_contains(cr_key)
                    &&& s.reconcile_state_of(cr_key).local_state.reconcile_pc === simple_reconciler::init_pc()
                    &&& s.reconcile_state_of(cr_key).pending_req_msg.is_None()
            }))
        )),
{
    let invariant = |s: State<SimpleReconcileState>| {
        s.reconcile_state_contains(cr_key)
        && s.reconcile_state_of(cr_key).local_state.reconcile_pc === simple_reconciler::init_pc()
        ==> s.reconcile_state_contains(cr_key)
            && s.reconcile_state_of(cr_key).local_state.reconcile_pc === simple_reconciler::init_pc()
            && s.reconcile_state_of(cr_key).pending_req_msg.is_None()
    };
    init_invariant::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()), init(simple_reconciler()), next(simple_reconciler()), invariant);

    // We intentionally write the safety property in a form that is friendly to liveness reasoning
    // There is no need to do this if we only want to prove safety
    let invariant_temp_pred = lift_state(|s: State<SimpleReconcileState>| {
        &&& s.reconcile_state_contains(cr_key)
        &&& s.reconcile_state_of(cr_key).local_state.reconcile_pc === simple_reconciler::init_pc()
    }).implies(lift_state(|s: State<SimpleReconcileState>| {
        &&& s.reconcile_state_contains(cr_key)
        &&& s.reconcile_state_of(cr_key).local_state.reconcile_pc === simple_reconciler::init_pc()
        &&& s.reconcile_state_of(cr_key).pending_req_msg.is_None()
    }));
    temp_pred_equality::<State<SimpleReconcileState>>(lift_state(invariant), invariant_temp_pred);
}

pub proof fn lemma_always_reconcile_get_cr_done_implies_pending_get_cr_req(cr_key: ResourceKey)
    requires
        cr_key.kind.is_CustomResourceKind(),
    ensures
        sm_spec(simple_reconciler()).entails(always(
            lift_state(|s: State<SimpleReconcileState>| {
                &&& s.reconcile_state_contains(cr_key)
                &&& s.reconcile_state_of(cr_key).local_state.reconcile_pc === simple_reconciler::after_get_cr_pc()
            })
                .implies(lift_state(|s: State<SimpleReconcileState>| {
                    &&& s.reconcile_state_contains(cr_key)
                    &&& s.reconcile_state_of(cr_key).local_state.reconcile_pc === simple_reconciler::after_get_cr_pc()
                    &&& s.reconcile_state_of(cr_key).pending_req_msg === Option::Some(controller_req_msg(APIRequest::GetRequest(GetRequest{key: cr_key})))
                    &&& s.message_sent(controller_req_msg(APIRequest::GetRequest(GetRequest{key: cr_key})))
                }))
        )),
{
    let invariant = |s: State<SimpleReconcileState>| {
        s.reconcile_state_contains(cr_key)
        && s.reconcile_state_of(cr_key).local_state.reconcile_pc === simple_reconciler::after_get_cr_pc()
        ==> s.reconcile_state_contains(cr_key)
            && s.reconcile_state_of(cr_key).local_state.reconcile_pc === simple_reconciler::after_get_cr_pc()
            && s.reconcile_state_of(cr_key).pending_req_msg === Option::Some(controller_req_msg(APIRequest::GetRequest(GetRequest{key: cr_key})))
            && s.message_sent(controller_req_msg(APIRequest::GetRequest(GetRequest{key: cr_key})))
    };
    init_invariant::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()), init(simple_reconciler()), next(simple_reconciler()), invariant);

    let invariant_temp_pred = lift_state(|s: State<SimpleReconcileState>| {
        &&& s.reconcile_state_contains(cr_key)
        &&& s.reconcile_state_of(cr_key).local_state.reconcile_pc === simple_reconciler::after_get_cr_pc()
    }).implies(lift_state(|s: State<SimpleReconcileState>| {
        &&& s.reconcile_state_contains(cr_key)
        &&& s.reconcile_state_of(cr_key).local_state.reconcile_pc === simple_reconciler::after_get_cr_pc()
        &&& s.reconcile_state_of(cr_key).pending_req_msg === Option::Some(controller_req_msg(APIRequest::GetRequest(GetRequest{key: cr_key})))
        &&& s.message_sent(controller_req_msg(APIRequest::GetRequest(GetRequest{key: cr_key})))
    }));
    temp_pred_equality::<State<SimpleReconcileState>>(lift_state(invariant), invariant_temp_pred);
}

pub proof fn lemma_always_reconcile_create_cm_done_implies_pending_create_cm_req(cr_key: ResourceKey)
    requires
        cr_key.kind.is_CustomResourceKind(),
    ensures
        sm_spec(simple_reconciler()).entails(always(
            lift_state(|s: State<SimpleReconcileState>| {
                &&& s.reconcile_state_contains(cr_key)
                &&& s.reconcile_state_of(cr_key).local_state.reconcile_pc === simple_reconciler::after_create_cm_pc()
            })
                .implies(lift_state(|s: State<SimpleReconcileState>| {
                    &&& s.reconcile_state_contains(cr_key)
                    &&& s.reconcile_state_of(cr_key).local_state.reconcile_pc === simple_reconciler::after_create_cm_pc()
                    &&& s.reconcile_state_of(cr_key).pending_req_msg === Option::Some(controller_req_msg(simple_reconciler::create_cm_req(cr_key)))
                    &&& s.message_sent(controller_req_msg(simple_reconciler::create_cm_req(cr_key)))
                }))
        )),
{
    let invariant = |s: State<SimpleReconcileState>| {
        s.reconcile_state_contains(cr_key)
        && s.reconcile_state_of(cr_key).local_state.reconcile_pc === simple_reconciler::after_create_cm_pc()
        ==> s.reconcile_state_contains(cr_key)
            && s.reconcile_state_of(cr_key).local_state.reconcile_pc === simple_reconciler::after_create_cm_pc()
            && s.reconcile_state_of(cr_key).pending_req_msg === Option::Some(controller_req_msg(simple_reconciler::create_cm_req(cr_key)))
            && s.message_sent(controller_req_msg(simple_reconciler::create_cm_req(cr_key)))
    };
    init_invariant::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()), init(simple_reconciler()), next(simple_reconciler()), invariant);

    let invariant_temp_pred = lift_state(|s: State<SimpleReconcileState>| {
        &&& s.reconcile_state_contains(cr_key)
        &&& s.reconcile_state_of(cr_key).local_state.reconcile_pc === simple_reconciler::after_create_cm_pc()
    }).implies(lift_state(|s: State<SimpleReconcileState>| {
        &&& s.reconcile_state_contains(cr_key)
        &&& s.reconcile_state_of(cr_key).local_state.reconcile_pc === simple_reconciler::after_create_cm_pc()
        &&& s.reconcile_state_of(cr_key).pending_req_msg === Option::Some(controller_req_msg(simple_reconciler::create_cm_req(cr_key)))
        &&& s.message_sent(controller_req_msg(simple_reconciler::create_cm_req(cr_key)))
    }));
    temp_pred_equality::<State<SimpleReconcileState>>(lift_state(invariant), invariant_temp_pred);
}

pub proof fn lemma_delete_cm_req_msg_never_sent(cr_key: ResourceKey)
    requires
        cr_key.kind.is_CustomResourceKind(),
    ensures
        sm_spec(simple_reconciler()).entails(always(
            lift_state(|s: State<SimpleReconcileState>| !exists |m: Message| {
                &&& #[trigger] s.message_sent(m)
                &&& m.dst === HostId::KubernetesAPI
                &&& m.is_delete_request()
                &&& m.get_delete_request().key === simple_reconciler::subresource_configmap(cr_key).key
            })
        )),
{
    let invariant = |s: State<SimpleReconcileState>| !exists |m: Message| {
        &&& #[trigger] s.message_sent(m)
        &&& m.dst === HostId::KubernetesAPI
        &&& m.is_delete_request()
        &&& m.get_delete_request().key === simple_reconciler::subresource_configmap(cr_key).key
    };
    init_invariant::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()), init(simple_reconciler()), next(simple_reconciler()), invariant);
}

}