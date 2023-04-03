// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::{common::*, custom_resource::*, object::*};
use crate::kubernetes_cluster::{
    proof::{
        controller_runtime_liveness, controller_runtime_safety, kubernetes_api_liveness,
        kubernetes_api_safety,
        cluster::*,
    },
    spec::{
        controller::common::{controller_req_msg, ControllerActionInput},
        controller::controller_runtime::{continue_reconcile, end_reconcile},
        controller::state_machine::controller,
        distributed_system::*,
        message::*,
    },
};
use crate::pervasive::*;
use crate::pervasive::{option::*, result::*};
use crate::simple_controller::proof::safety::*;
use crate::simple_controller::proof::shared::*;
use crate::simple_controller::spec::{
    simple_reconciler,
    simple_reconciler::{simple_reconciler, SimpleReconcileState},
};
use crate::temporal_logic::{defs::*, rules::*};
use builtin::*;
use builtin_macros::*;

verus! {

spec fn cr_exists(cr: CustomResourceView) -> TempPred<State<SimpleReconcileState>> {
    lift_state(|s: State<SimpleReconcileState>| s.resource_obj_exists(KubernetesObject::CustomResource(cr)))
}

spec fn cr_matched(cr: CustomResourceView) -> TempPred<State<SimpleReconcileState>> {
    lift_state(|s: State<SimpleReconcileState>| s.resource_key_exists(simple_reconciler::subresource_configmap(cr.object_ref()).object_ref()))
}

spec fn all_invariants(cr: CustomResourceView) -> TempPred<State<SimpleReconcileState>> {
    always(lift_state(reconcile_create_cm_done_implies_pending_create_cm_req_in_flight_or_cm_exists(cr)))
    .and(tla_forall(|msg| always(lift_state(controller_runtime_safety::resp_matches_at_most_one_pending_req(msg, cr.object_ref())))))
    .and(always(lift_state(reconcile_get_cr_done_implies_pending_req_in_flight_or_resp_in_flight(cr))))
    .and(always(lift_state(reconciler_at_init_pc(cr)).implies(lift_state(reconcile_init_pc_and_no_pending_req(cr)))))
}

spec fn partial_spec_with_invariants_and_cr_always_exists(cr: CustomResourceView) -> TempPred<State<SimpleReconcileState>> {
    sm_partial_spec(simple_reconciler())
    .and(all_invariants(cr))
    .and(always(cr_exists(cr)))
}

spec fn liveness(cr: CustomResourceView) -> TempPred<State<SimpleReconcileState>> {
    always(cr_exists(cr)).leads_to(always(cr_matched(cr)))
}

proof fn liveness_proof_forall_cr()
    ensures
        forall |cr: CustomResourceView| #[trigger] sm_spec(simple_reconciler()).entails(liveness(cr)),
{
    assert forall |cr: CustomResourceView| #[trigger] sm_spec(simple_reconciler()).entails(liveness(cr)) by {
        liveness_proof(cr);
    };
}

proof fn liveness_proof(cr: CustomResourceView)
    ensures
        sm_spec(simple_reconciler()).entails(
            always(cr_exists(cr)).leads_to(always(cr_matched(cr)))
        ),
{
    lemma_valid_stable_sm_partial_spec_and_invariants(cr);
    lemma_true_leads_to_cm_exists_with_invariant(cr);
    unpack_assumption_from_spec::<State<SimpleReconcileState>>(lift_state(init(simple_reconciler())), sm_partial_spec(simple_reconciler()).and(all_invariants(cr)), always(cr_exists(cr)), lift_state(cm_exists(cr)));

    temp_pred_equality::<State<SimpleReconcileState>>(lift_state(init(simple_reconciler())).and(sm_partial_spec(simple_reconciler()).and(all_invariants(cr))), sm_spec(simple_reconciler()).and(all_invariants(cr)));

    lemma_sm_spec_entails_all_invariants(cr);
    minimize_spec::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()), all_invariants(cr), always(cr_exists(cr)).leads_to(lift_state(cm_exists(cr))));

    lemma_p_leads_to_cm_always_exists(cr, always(cr_exists(cr)));
}

proof fn lemma_sm_spec_entails_all_invariants(cr: CustomResourceView)
    ensures
        sm_spec(simple_reconciler()).entails(all_invariants(cr)),
{
    lemma_always_reconcile_create_cm_done_implies_pending_create_cm_req_in_flight_or_cm_exists(cr);
    controller_runtime_safety::lemma_always_forall_resp_matches_at_most_one_pending_req(simple_reconciler(), cr.object_ref());
    lemma_always_reconcile_get_cr_done_implies_pending_req_in_flight_or_resp_in_flight(cr);
    lemma_always_reconcile_init_pc_and_no_pending_req(cr);

    entails_and_temp::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()), always(lift_state(reconcile_create_cm_done_implies_pending_create_cm_req_in_flight_or_cm_exists(cr))), tla_forall(|msg| always(lift_state(controller_runtime_safety::resp_matches_at_most_one_pending_req(msg, cr.object_ref())))));

    entails_and_temp::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()), always(lift_state(reconcile_create_cm_done_implies_pending_create_cm_req_in_flight_or_cm_exists(cr))).and(tla_forall(|msg| always(lift_state(controller_runtime_safety::resp_matches_at_most_one_pending_req(msg, cr.object_ref()))))), always(lift_state(reconcile_get_cr_done_implies_pending_req_in_flight_or_resp_in_flight(cr))));

    entails_and_temp::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()), always(lift_state(reconcile_create_cm_done_implies_pending_create_cm_req_in_flight_or_cm_exists(cr))).and(tla_forall(|msg| always(lift_state(controller_runtime_safety::resp_matches_at_most_one_pending_req(msg, cr.object_ref()))))).and(always(lift_state(reconcile_get_cr_done_implies_pending_req_in_flight_or_resp_in_flight(cr)))), always(lift_state(reconciler_at_init_pc(cr)).implies(lift_state(reconcile_init_pc_and_no_pending_req(cr)))));
}

proof fn lemma_valid_stable_sm_partial_spec_and_invariants(cr: CustomResourceView)
    ensures
        valid(stable(sm_partial_spec(simple_reconciler()).and(all_invariants(cr)))),
{
    valid_stable_sm_partial_spec::<SimpleReconcileState>(simple_reconciler());

    always_p_stable::<State<SimpleReconcileState>>(lift_state(reconcile_create_cm_done_implies_pending_create_cm_req_in_flight_or_cm_exists(cr)));
    always_p_stable::<State<SimpleReconcileState>>(lift_state(reconcile_get_cr_done_implies_pending_req_in_flight_or_resp_in_flight(cr)));
    always_p_stable::<State<SimpleReconcileState>>(tla_forall(|msg| lift_state(controller_runtime_safety::resp_matches_at_most_one_pending_req(msg, cr.object_ref()))));
    always_p_stable::<State<SimpleReconcileState>>(lift_state(reconciler_at_init_pc(cr)).implies(lift_state(reconcile_init_pc_and_no_pending_req(cr))));

    let a_to_p = |msg| lift_state(controller_runtime_safety::resp_matches_at_most_one_pending_req::<SimpleReconcileState>(msg, cr.object_ref()));
    let a_to_always = |msg| always(lift_state(controller_runtime_safety::resp_matches_at_most_one_pending_req::<SimpleReconcileState>(msg, cr.object_ref())));
    tla_forall_always_equality_variant::<State<SimpleReconcileState>, Message>(a_to_always, a_to_p);

    stable_and_temp::<State<SimpleReconcileState>>(always(lift_state(reconcile_create_cm_done_implies_pending_create_cm_req_in_flight_or_cm_exists(cr))), tla_forall(|msg| always(lift_state(controller_runtime_safety::resp_matches_at_most_one_pending_req(msg, cr.object_ref())))));
    stable_and_temp::<State<SimpleReconcileState>>(always(lift_state(reconcile_create_cm_done_implies_pending_create_cm_req_in_flight_or_cm_exists(cr))).and(tla_forall(|msg| always(lift_state(controller_runtime_safety::resp_matches_at_most_one_pending_req(msg, cr.object_ref()))))), always(lift_state(reconcile_get_cr_done_implies_pending_req_in_flight_or_resp_in_flight(cr))));
    stable_and_temp::<State<SimpleReconcileState>>(always(lift_state(reconcile_create_cm_done_implies_pending_create_cm_req_in_flight_or_cm_exists(cr))).and(tla_forall(|msg| always(lift_state(controller_runtime_safety::resp_matches_at_most_one_pending_req(msg, cr.object_ref()))))).and(always(lift_state(reconcile_get_cr_done_implies_pending_req_in_flight_or_resp_in_flight(cr)))), always(lift_state(reconciler_at_init_pc(cr)).implies(lift_state(reconcile_init_pc_and_no_pending_req(cr)))));

    stable_and_temp::<State<SimpleReconcileState>>(sm_partial_spec(simple_reconciler()), all_invariants(cr));
}

proof fn lemma_true_leads_to_cm_exists_with_invariant(cr: CustomResourceView)
    ensures
        partial_spec_with_invariants_and_cr_always_exists(cr).entails(
            true_pred::<State<SimpleReconcileState>>().leads_to(lift_state(cm_exists(cr)))
        ),
{
    lemma_reconcile_idle_leads_to_cm_exists_with_invariant(cr);
    lemma_reconcile_ongoing_leads_to_cm_exists_with_invariant(cr);

    temp_pred_equality::<State<SimpleReconcileState>>(true_pred::<State<SimpleReconcileState>>(), lift_state(|s: State<SimpleReconcileState>| s.reconcile_state_contains(cr.object_ref())).or(lift_state(|s: State<SimpleReconcileState>| !s.reconcile_state_contains(cr.object_ref()))));

    or_leads_to_combine_temp(partial_spec_with_invariants_and_cr_always_exists(cr), lift_state(|s: State<SimpleReconcileState>| s.reconcile_state_contains(cr.object_ref())), lift_state(|s: State<SimpleReconcileState>| !s.reconcile_state_contains(cr.object_ref())), lift_state(cm_exists(cr)));
}

proof fn lemma_reconcile_idle_leads_to_cm_exists_with_invariant(cr: CustomResourceView)
    ensures
        partial_spec_with_invariants_and_cr_always_exists(cr).entails(
        lift_state(|s: State<SimpleReconcileState>| !s.reconcile_state_contains(cr.object_ref()))
            .leads_to(lift_state(cm_exists(cr)))
        ),
{
    controller_runtime_liveness::lemma_cr_always_exists_entails_reconcile_idle_leads_to_reconcile_init_and_no_pending_req::<SimpleReconcileState>(simple_reconciler(), cr.object_ref());

    temp_pred_equality::<State<SimpleReconcileState>>(lift_state(reconcile_init_pc_and_no_pending_req(cr)), lift_state(|s: State<SimpleReconcileState>| {
        &&& s.reconcile_state_contains(cr.object_ref())
        &&& s.reconcile_state_of(cr.object_ref()).local_state == (simple_reconciler().reconcile_init_state)()
        &&& s.reconcile_state_of(cr.object_ref()).pending_req_msg.is_None()
    }));
    
    assert(sm_partial_spec(simple_reconciler()).and(always(lift_state(|s: State<SimpleReconcileState>| s.resource_key_exists(cr.object_ref())))).entails(lift_state(|s: State<SimpleReconcileState>| {!s.reconcile_state_contains(cr.object_ref())}).leads_to(lift_state(reconcile_init_pc_and_no_pending_req(cr)))));

    implies_preserved_by_always_temp::<State<SimpleReconcileState>>(cr_exists(cr), lift_state(|s: State<SimpleReconcileState>| s.resource_key_exists(cr.object_ref())));
    assert(valid(always(cr_exists(cr)).implies(always(lift_state(|s: State<SimpleReconcileState>| s.resource_key_exists(cr.object_ref()))))));

    partially_strengthen_spec::<State<SimpleReconcileState>>(sm_partial_spec(simple_reconciler()), always(cr_exists(cr)), always(lift_state(|s: State<SimpleReconcileState>| s.resource_key_exists(cr.object_ref()))), lift_state(|s: State<SimpleReconcileState>| {!s.reconcile_state_contains(cr.object_ref())}).leads_to(lift_state(reconcile_init_pc_and_no_pending_req(cr))));

    strengthen_spec::<State<SimpleReconcileState>>(sm_partial_spec(simple_reconciler()).and(always(cr_exists(cr))), all_invariants(cr), lift_state(|s: State<SimpleReconcileState>| {!s.reconcile_state_contains(cr.object_ref())}).leads_to(lift_state(reconcile_init_pc_and_no_pending_req(cr))));

    temp_pred_equality::<State<SimpleReconcileState>>(partial_spec_with_invariants_and_cr_always_exists(cr), sm_partial_spec(simple_reconciler()).and(always(cr_exists(cr))).and(all_invariants(cr)));

    lemma_init_pc_and_no_pending_req_leads_to_cm_exists_with_invariant(cr);
    leads_to_trans::<State<SimpleReconcileState>>(partial_spec_with_invariants_and_cr_always_exists(cr), |s: State<SimpleReconcileState>| {!s.reconcile_state_contains(cr.object_ref())}, reconcile_init_pc_and_no_pending_req(cr), cm_exists(cr));
}

proof fn lemma_reconcile_ongoing_leads_to_cm_exists_with_invariant(cr: CustomResourceView)
    ensures
        partial_spec_with_invariants_and_cr_always_exists(cr).entails(
        lift_state(|s: State<SimpleReconcileState>| s.reconcile_state_contains(cr.object_ref()))
            .leads_to(lift_state(cm_exists(cr)))
        ),
{
    temp_pred_equality::<State<SimpleReconcileState>>(lift_state(|s: State<SimpleReconcileState>| s.reconcile_state_contains(cr.object_ref())), lift_state(reconciler_reconcile_error(cr)).or(lift_state(reconciler_at_init_pc(cr))).or(lift_state(reconciler_at_after_get_cr_pc(cr))).or(lift_state(reconciler_at_after_create_cm_pc(cr))));
    lemma_error_pc_leads_to_cm_exists_with_invariant(cr);
    lemma_init_pc_leads_to_cm_exists_with_invariant(cr);
    lemma_after_get_cr_pc_leads_to_cm_exists_with_invariant(cr);
    lemma_after_create_cm_pc_leads_to_cm_exists_with_invariant(cr);
    or_leads_to_combine_temp::<State<SimpleReconcileState>>(partial_spec_with_invariants_and_cr_always_exists(cr), lift_state(reconciler_reconcile_error(cr)), lift_state(reconciler_at_init_pc(cr)), lift_state(cm_exists(cr)));
    or_leads_to_combine_temp::<State<SimpleReconcileState>>(partial_spec_with_invariants_and_cr_always_exists(cr), lift_state(reconciler_reconcile_error(cr)).or(lift_state(reconciler_at_init_pc(cr))), lift_state(reconciler_at_after_get_cr_pc(cr)), lift_state(cm_exists(cr)));
    or_leads_to_combine_temp::<State<SimpleReconcileState>>(partial_spec_with_invariants_and_cr_always_exists(cr), lift_state(reconciler_reconcile_error(cr)).or(lift_state(reconciler_at_init_pc(cr))).or(lift_state(reconciler_at_after_get_cr_pc(cr))), lift_state(reconciler_at_after_create_cm_pc(cr)), lift_state(cm_exists(cr)));
}

proof fn lemma_error_pc_leads_to_cm_exists_with_invariant(cr: CustomResourceView)
    ensures
        partial_spec_with_invariants_and_cr_always_exists(cr).entails(
        lift_state(reconciler_reconcile_error(cr))
            .leads_to(lift_state(cm_exists(cr)))
        ),
{
    controller_runtime_liveness::lemma_cr_always_exists_entails_reconcile_error_leads_to_reconcile_init_and_no_pending_req::<SimpleReconcileState>(simple_reconciler(), cr.object_ref());

    temp_pred_equality::<State<SimpleReconcileState>>(lift_state(reconcile_init_pc_and_no_pending_req(cr)), lift_state(|s: State<SimpleReconcileState>| {
        &&& s.reconcile_state_contains(cr.object_ref())
        &&& s.reconcile_state_of(cr.object_ref()).local_state == (simple_reconciler().reconcile_init_state)()
        &&& s.reconcile_state_of(cr.object_ref()).pending_req_msg.is_None()
    }));
    
    assert(sm_partial_spec(simple_reconciler()).and(always(lift_state(|s: State<SimpleReconcileState>| s.resource_key_exists(cr.object_ref())))).entails(lift_state(reconciler_reconcile_error(cr)).leads_to(lift_state(reconcile_init_pc_and_no_pending_req(cr)))));

    implies_preserved_by_always_temp::<State<SimpleReconcileState>>(cr_exists(cr), lift_state(|s: State<SimpleReconcileState>| s.resource_key_exists(cr.object_ref())));
    assert(valid(always(cr_exists(cr)).implies(always(lift_state(|s: State<SimpleReconcileState>| s.resource_key_exists(cr.object_ref()))))));

    partially_strengthen_spec::<State<SimpleReconcileState>>(sm_partial_spec(simple_reconciler()), always(cr_exists(cr)), always(lift_state(|s: State<SimpleReconcileState>| s.resource_key_exists(cr.object_ref()))), lift_state(reconciler_reconcile_error(cr)).leads_to(lift_state(reconcile_init_pc_and_no_pending_req(cr))));

    strengthen_spec::<State<SimpleReconcileState>>(sm_partial_spec(simple_reconciler()).and(always(cr_exists(cr))), all_invariants(cr), lift_state(reconciler_reconcile_error(cr)).leads_to(lift_state(reconcile_init_pc_and_no_pending_req(cr))));

    temp_pred_equality::<State<SimpleReconcileState>>(partial_spec_with_invariants_and_cr_always_exists(cr), sm_partial_spec(simple_reconciler()).and(always(cr_exists(cr))).and(all_invariants(cr)));

    lemma_init_pc_and_no_pending_req_leads_to_cm_exists_with_invariant(cr);
    leads_to_trans::<State<SimpleReconcileState>>(partial_spec_with_invariants_and_cr_always_exists(cr), reconciler_reconcile_error(cr), reconcile_init_pc_and_no_pending_req(cr), cm_exists(cr));
}

proof fn lemma_init_pc_leads_to_cm_exists_with_invariant(cr: CustomResourceView)
    ensures
        partial_spec_with_invariants_and_cr_always_exists(cr).entails(
            lift_state(reconciler_at_init_pc(cr))
                .leads_to(lift_state(cm_exists(cr)))
        ),
{
    implies_to_leads_to::<State<SimpleReconcileState>>(partial_spec_with_invariants_and_cr_always_exists(cr), lift_state(reconciler_at_init_pc(cr)), lift_state(reconcile_init_pc_and_no_pending_req(cr)));
    
    lemma_init_pc_and_no_pending_req_leads_to_cm_exists_with_invariant(cr);
    leads_to_trans::<State<SimpleReconcileState>>(partial_spec_with_invariants_and_cr_always_exists(cr), reconciler_at_init_pc(cr), reconcile_init_pc_and_no_pending_req(cr), cm_exists(cr));
}

proof fn lemma_init_pc_and_no_pending_req_leads_to_cm_exists_with_invariant(cr: CustomResourceView)
    ensures
        partial_spec_with_invariants_and_cr_always_exists(cr).entails(
            lift_state(reconciler_at_init_pc_and_no_pending_req(cr))
                .leads_to(lift_state(cm_exists(cr)))
        ),
{
    lemma_init_pc_leads_to_after_get_cr_pc(cr);

    temp_pred_equality::<State<SimpleReconcileState>>(partial_spec_with_invariants_and_cr_always_exists(cr), sm_partial_spec(simple_reconciler()).and(all_invariants(cr).and(always(cr_exists(cr)))));

    strengthen_spec(sm_partial_spec(simple_reconciler()), all_invariants(cr).and(always(cr_exists(cr))), lift_state(reconciler_at_init_pc_and_no_pending_req(cr)).leads_to(lift_state(reconciler_at_after_get_cr_pc(cr))));

    lemma_after_get_cr_pc_leads_to_cm_exists_with_invariant(cr);
    leads_to_trans::<State<SimpleReconcileState>>(partial_spec_with_invariants_and_cr_always_exists(cr), reconciler_at_init_pc_and_no_pending_req(cr), reconciler_at_after_get_cr_pc(cr), cm_exists(cr));
}

proof fn lemma_after_get_cr_pc_leads_to_cm_exists_with_invariant(cr: CustomResourceView)
    ensures
        partial_spec_with_invariants_and_cr_always_exists(cr).entails(
            lift_state(reconciler_at_after_get_cr_pc(cr))
                .leads_to(lift_state(cm_exists(cr)))
        ),
{
    assert forall |ex| partial_spec_with_invariants_and_cr_always_exists(cr).satisfied_by(ex) implies #[trigger] lift_state(reconciler_at_after_get_cr_pc(cr)).leads_to(lift_state(reconciler_at_after_create_cm_pc(cr))).satisfied_by(ex) by {
        assert forall |i| #[trigger] lift_state(reconciler_at_after_get_cr_pc(cr)).satisfied_by(ex.suffix(i)) implies eventually(lift_state(reconciler_at_after_create_cm_pc(cr))).satisfied_by(ex.suffix(i)) by {
            assert(lift_state(reconcile_get_cr_done_implies_pending_req_in_flight_or_resp_in_flight(cr)).satisfied_by(ex.suffix(i)));
            let s = ex.suffix(i).head();
            let req_msg = choose |req_msg: Message| {
                #[trigger] is_controller_get_cr_request_msg(req_msg, cr)
                && s.reconcile_state_of(cr.object_ref()).pending_req_msg == Option::Some(req_msg)
                && (s.message_in_flight(req_msg)
                    || exists |resp_msg: Message| {
                        #[trigger] s.message_in_flight(resp_msg)
                        && resp_msg_matches_req_msg(resp_msg, req_msg)
                    })
            };
            if (s.message_in_flight(req_msg)) {
                lemma_req_msg_sent_and_after_get_cr_pc_leads_to_after_create_cm_pc_with_invariant(req_msg, cr);
                instantiate_entailed_leads_to::<State<SimpleReconcileState>>(ex, i, sm_partial_spec(simple_reconciler()).and(tla_forall(|msg| always(lift_state(controller_runtime_safety::resp_matches_at_most_one_pending_req(msg, cr.object_ref()))))), lift_state(reconciler_at_after_get_cr_pc_and_pending_req_and_req_in_flight(req_msg, cr)), lift_state(reconciler_at_after_create_cm_pc(cr)));
            } else {
                lemma_exists_resp_msg_sent_and_after_get_cr_pc_leads_to_after_create_cm_pc_with_invariant(req_msg, cr);
                instantiate_entailed_leads_to::<State<SimpleReconcileState>>(ex, i, sm_partial_spec(simple_reconciler()).and(tla_forall(|msg| always(lift_state(controller_runtime_safety::resp_matches_at_most_one_pending_req(msg, cr.object_ref()))))), lift_state(|s: State<SimpleReconcileState>| {
                    exists |m: Message| {
                        &&& #[trigger] s.message_in_flight(m)
                        &&& resp_msg_matches_req_msg(m, req_msg)
                    }
                }).and(lift_state(reconciler_at_after_get_cr_pc_and_pending_req(req_msg, cr))), lift_state(reconciler_at_after_create_cm_pc(cr)));
            }
        }
    }
    lemma_after_create_cm_pc_leads_to_cm_exists_with_invariant(cr);
    leads_to_trans::<State<SimpleReconcileState>>(partial_spec_with_invariants_and_cr_always_exists(cr), reconciler_at_after_get_cr_pc(cr), reconciler_at_after_create_cm_pc(cr), cm_exists(cr));
}

proof fn lemma_after_create_cm_pc_leads_to_cm_exists_with_invariant(cr: CustomResourceView)
    ensures
        partial_spec_with_invariants_and_cr_always_exists(cr).entails(
            lift_state(reconciler_at_after_create_cm_pc(cr))
                .leads_to(lift_state(cm_exists(cr)))
        ),
{
    assert forall |ex| #[trigger] partial_spec_with_invariants_and_cr_always_exists(cr).satisfied_by(ex) implies
    lift_state(reconciler_at_after_create_cm_pc(cr)).leads_to(lift_state(cm_exists(cr))).satisfied_by(ex) by {
        assert forall |i| #[trigger] lift_state(reconciler_at_after_create_cm_pc(cr)).satisfied_by(ex.suffix(i))
        implies eventually(lift_state(cm_exists(cr))).satisfied_by(ex.suffix(i)) by {
            assert(lift_state(reconcile_create_cm_done_implies_pending_create_cm_req_in_flight_or_cm_exists(cr)).satisfied_by(ex.suffix(i)));
            let s = ex.suffix(i).head();
            let req_msg = choose |m: Message| {
                (#[trigger] is_controller_create_cm_request_msg(m, cr)
                && s.reconcile_state_of(cr.object_ref()).pending_req_msg == Option::Some(m)
                && s.message_in_flight(m))
                || s.resource_key_exists(simple_reconciler::subresource_configmap(cr.object_ref()).object_ref())
            };
            if (s.resource_key_exists(simple_reconciler::subresource_configmap(cr.object_ref()).object_ref())) {
                assert(lift_state(cm_exists(cr)).satisfied_by(ex.suffix(i).suffix(0)));
            } else {
                let cm = KubernetesObject::ConfigMap(simple_reconciler::subresource_configmap(cr.object_ref()));
                let pre = |s: State<SimpleReconcileState>| {
                    &&& s.message_in_flight(req_msg) &&& req_msg.dst == HostId::KubernetesAPI &&& req_msg.content.is_create_request() 
                    &&& req_msg.content.get_create_request().obj == cm
                };
                kubernetes_api_liveness::lemma_create_req_leads_to_res_exists::<SimpleReconcileState>(sm_partial_spec(simple_reconciler()), simple_reconciler(), req_msg, cm);
                instantiate_entailed_leads_to::<State<SimpleReconcileState>>(ex, i, sm_partial_spec(simple_reconciler()), lift_state(pre), lift_state(cm_exists(cr)));
            }
        };
    };
}

proof fn lemma_p_leads_to_cm_always_exists(cr: CustomResourceView, p: TempPred<State<SimpleReconcileState>>)
    requires
        sm_spec(simple_reconciler()).entails(
            p.leads_to(lift_state(cm_exists(cr)))
        ),
    ensures
        sm_spec(simple_reconciler()).entails(
            p.leads_to(always(lift_state(cm_exists(cr))))
        ),
{
    let next_and_invariant = |s: State<SimpleReconcileState>, s_prime: State<SimpleReconcileState>| {
        &&& next(simple_reconciler())(s, s_prime)
        &&& delete_cm_req_msg_not_in_flight(cr)(s)
    };

    lemma_delete_cm_req_msg_never_in_flight(cr);

    strengthen_next::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()), next(simple_reconciler()), delete_cm_req_msg_not_in_flight(cr), next_and_invariant);
    leads_to_stable_temp::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()), lift_action(next_and_invariant), p, lift_state(cm_exists(cr)));
}

proof fn lemma_init_pc_leads_to_after_get_cr_pc(cr: CustomResourceView)
    ensures
        sm_partial_spec(simple_reconciler()).entails(
            lift_state(reconciler_at_init_pc_and_no_pending_req(cr)).leads_to(lift_state(reconciler_at_after_get_cr_pc(cr)))
        ),
{
    let pre = reconciler_at_init_pc_and_no_pending_req(cr);
    let post = reconciler_at_after_get_cr_pc(cr);
    let input = ControllerActionInput {
        recv: Option::None,
        scheduled_cr_key: Option::Some(cr.object_ref()),
    };
    controller_runtime_liveness::lemma_pre_leads_to_post_by_controller::<SimpleReconcileState>(sm_partial_spec(simple_reconciler()), simple_reconciler(), input, next(simple_reconciler()), continue_reconcile(simple_reconciler()), pre, post);
}

proof fn lemma_req_msg_sent_and_after_get_cr_pc_leads_to_after_create_cm_pc(req_msg: Message, cr: CustomResourceView)
    ensures
        sm_spec(simple_reconciler()).entails(
            lift_state(reconciler_at_after_get_cr_pc_and_pending_req_and_req_in_flight(req_msg, cr))
                .leads_to(lift_state(reconciler_at_after_create_cm_pc(cr)))
        ),
{
    let pre = reconciler_at_after_get_cr_pc_and_pending_req_and_req_in_flight(req_msg, cr);
    let get_cr_resp_msg_sent = |s: State<SimpleReconcileState>| {
        exists |resp_msg: Message| {
            &&& #[trigger] s.message_in_flight(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, req_msg)
        }
    };
    let reconciler_at_after_create_cm_pc = reconciler_at_after_create_cm_pc(cr);

    leads_to_weaken_auto::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()));

    leads_to_self::<State<SimpleReconcileState>>(pre);

    kubernetes_api_liveness::lemma_get_req_leads_to_some_resp::<SimpleReconcileState>(sm_spec(simple_reconciler()), simple_reconciler(), req_msg, cr.object_ref());

    // Now we have:
    //  spec |= pre ~> reconciler_at_after_get_cr_pc_and_pending_req /\ get_cr_req_in_flight
    //  spec |= get_cr_req_in_flight ~> get_cr_resp_msg_sent
    // By applying leads_to_partial_confluence, we will get spec |= pre ~> reconciler_at_after_get_cr_pc_and_pending_req /\ get_cr_resp_msg_sent
    leads_to_partial_confluence::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()), next(simple_reconciler()), pre, reconciler_at_after_get_cr_pc_and_pending_req(req_msg, cr), get_cr_req_in_flight(req_msg, cr), get_cr_resp_msg_sent);
    // Now we have all the premise to fire the leads-to formula from lemma_exists_resp_msg_sent_and_after_get_cr_pc_leads_to_after_create_cm_pc
    lemma_exists_resp_msg_sent_and_after_get_cr_pc_leads_to_after_create_cm_pc(req_msg, cr);
    leads_to_trans::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()),
        pre,
        |s| {
            &&& reconciler_at_after_get_cr_pc_and_pending_req(req_msg, cr)(s)
            &&& get_cr_resp_msg_sent(s)
        },
        reconciler_at_after_create_cm_pc
    );
}

proof fn lemma_req_msg_sent_and_after_get_cr_pc_leads_to_after_create_cm_pc_with_invariant(req_msg: Message, cr: CustomResourceView)
    ensures
    sm_partial_spec(simple_reconciler()).and(tla_forall(|msg| always(lift_state(controller_runtime_safety::resp_matches_at_most_one_pending_req(msg, cr.object_ref()))))).entails(
            lift_state(reconciler_at_after_get_cr_pc_and_pending_req_and_req_in_flight(req_msg, cr))
                .leads_to(lift_state(reconciler_at_after_create_cm_pc(cr)))
        ),
{
    let pre = reconciler_at_after_get_cr_pc_and_pending_req_and_req_in_flight(req_msg, cr);
    let get_cr_resp_msg_sent = |s: State<SimpleReconcileState>| {
        exists |resp_msg: Message| {
            &&& #[trigger] s.message_in_flight(resp_msg)
            &&& resp_msg_matches_req_msg(resp_msg, req_msg)
        }
    };
    let reconciler_at_after_create_cm_pc = reconciler_at_after_create_cm_pc(cr);

    leads_to_weaken_auto::<State<SimpleReconcileState>>(sm_partial_spec(simple_reconciler()).and(tla_forall(|msg| always(lift_state(controller_runtime_safety::resp_matches_at_most_one_pending_req(msg, cr.object_ref()))))));

    leads_to_self::<State<SimpleReconcileState>>(pre);

    kubernetes_api_liveness::lemma_get_req_leads_to_some_resp::<SimpleReconcileState>(sm_partial_spec(simple_reconciler()).and(tla_forall(|msg| always(lift_state(controller_runtime_safety::resp_matches_at_most_one_pending_req(msg, cr.object_ref()))))), simple_reconciler(), req_msg, cr.object_ref());

    let get_req = |s: State<SimpleReconcileState>| {
        &&& s.message_in_flight(req_msg)
        &&& req_msg.dst == HostId::KubernetesAPI
        &&& req_msg.content.is_get_request()
        &&& req_msg.content.get_get_request().key == cr.object_ref()
    };

    // Now we have:
    //  spec |= pre ~> reconciler_at_after_get_cr_pc_and_pending_req /\ get_cr_req_in_flight
    //  spec |= get_cr_req_in_flight ~> get_cr_resp_msg_sent
    // By applying leads_to_partial_confluence, we will get spec |= pre ~> reconciler_at_after_get_cr_pc_and_pending_req /\ get_cr_resp_msg_sent
    leads_to_partial_confluence::<State<SimpleReconcileState>>(sm_partial_spec(simple_reconciler()).and(tla_forall(|msg| always(lift_state(controller_runtime_safety::resp_matches_at_most_one_pending_req(msg, cr.object_ref()))))), next(simple_reconciler()), pre, reconciler_at_after_get_cr_pc_and_pending_req(req_msg, cr), get_req, get_cr_resp_msg_sent);
    // Now we have all the premise to fire the leads-to formula from lemma_exists_resp_msg_sent_and_after_get_cr_pc_leads_to_after_create_cm_pc
    lemma_exists_resp_msg_sent_and_after_get_cr_pc_leads_to_after_create_cm_pc_with_invariant(req_msg, cr);
    leads_to_trans::<State<SimpleReconcileState>>(sm_partial_spec(simple_reconciler()).and(tla_forall(|msg| always(lift_state(controller_runtime_safety::resp_matches_at_most_one_pending_req(msg, cr.object_ref()))))),
        pre,
        |s| {
            &&& reconciler_at_after_get_cr_pc_and_pending_req(req_msg, cr)(s)
            &&& get_cr_resp_msg_sent(s)
        },
        reconciler_at_after_create_cm_pc
    );
}

proof fn lemma_resp_msg_sent_and_after_get_cr_pc_leads_to_after_create_cm_pc(resp_msg: Message, req_msg: Message, cr: CustomResourceView)
    ensures
        sm_spec(simple_reconciler()).entails(
            lift_state(|s: State<SimpleReconcileState>| {
                &&& s.message_in_flight(resp_msg)
                &&& resp_msg_matches_req_msg(resp_msg, req_msg)
                &&& reconciler_at_after_get_cr_pc_and_pending_req(req_msg, cr)(s)
            }).leads_to(lift_state(reconciler_at_after_create_cm_pc(cr)))
        ),
{
    let pre = |s: State<SimpleReconcileState>| {
        &&& s.message_in_flight(resp_msg)
        &&& resp_msg_matches_req_msg(resp_msg, req_msg)
        &&& reconciler_at_after_get_cr_pc_and_pending_req(req_msg, cr)(s)
    };
    let post = reconciler_at_after_create_cm_pc(cr);
    let input = ControllerActionInput {
        recv: Option::Some(resp_msg),
        scheduled_cr_key: Option::Some(cr.object_ref()),
    };

    let next_and_invariant = |s, s_prime: State<SimpleReconcileState>| {
        &&& next(simple_reconciler())(s, s_prime)
        &&& controller_runtime_safety::resp_matches_at_most_one_pending_req(resp_msg, cr.object_ref())(s)
    };

    controller_runtime_safety::lemma_always_resp_matches_at_most_one_pending_req::<SimpleReconcileState>(simple_reconciler(), resp_msg, cr.object_ref());

    strengthen_next::<State<SimpleReconcileState>>(sm_spec(simple_reconciler()), next(simple_reconciler()), controller_runtime_safety::resp_matches_at_most_one_pending_req(resp_msg, cr.object_ref()), next_and_invariant);
    controller_runtime_liveness::lemma_pre_leads_to_post_by_controller::<SimpleReconcileState>(sm_spec(simple_reconciler()), simple_reconciler(), input, next_and_invariant, continue_reconcile(simple_reconciler()), pre, post);
}

proof fn lemma_resp_msg_sent_and_after_get_cr_pc_leads_to_after_create_cm_pc_with_invariant(resp_msg: Message, req_msg: Message, cr: CustomResourceView)
    ensures
        sm_partial_spec(simple_reconciler()).and(tla_forall(|msg| always(lift_state(controller_runtime_safety::resp_matches_at_most_one_pending_req(msg, cr.object_ref()))))).entails(
            lift_state(|s: State<SimpleReconcileState>| {
                &&& s.message_in_flight(resp_msg)
                &&& resp_msg_matches_req_msg(resp_msg, req_msg)
                &&& reconciler_at_after_get_cr_pc_and_pending_req(req_msg, cr)(s)
            }).leads_to(lift_state(reconciler_at_after_create_cm_pc(cr)))
        ),
{
    let pre = |s: State<SimpleReconcileState>| {
        &&& s.message_in_flight(resp_msg)
        &&& resp_msg_matches_req_msg(resp_msg, req_msg)
        &&& reconciler_at_after_get_cr_pc_and_pending_req(req_msg, cr)(s)
    };
    let post = reconciler_at_after_create_cm_pc(cr);
    let input = ControllerActionInput {
        recv: Option::Some(resp_msg),
        scheduled_cr_key: Option::Some(cr.object_ref()),
    };
    let next_and_invariant = |s, s_prime: State<SimpleReconcileState>| {
        &&& next(simple_reconciler())(s, s_prime)
        &&& controller_runtime_safety::resp_matches_at_most_one_pending_req(resp_msg, cr.object_ref())(s)
    };

    tla_forall_apply::<State<SimpleReconcileState>, Message>(|msg| always(lift_state(controller_runtime_safety::resp_matches_at_most_one_pending_req::<SimpleReconcileState>(msg, cr.object_ref()))), resp_msg);

    strengthen_next::<State<SimpleReconcileState>>(sm_partial_spec(simple_reconciler()).and(tla_forall(|msg| always(lift_state(controller_runtime_safety::resp_matches_at_most_one_pending_req(msg, cr.object_ref()))))), next(simple_reconciler()), controller_runtime_safety::resp_matches_at_most_one_pending_req(resp_msg, cr.object_ref()), next_and_invariant);

    controller_runtime_liveness::lemma_pre_leads_to_post_by_controller::<SimpleReconcileState>(sm_partial_spec(simple_reconciler()).and(tla_forall(|msg| always(lift_state(controller_runtime_safety::resp_matches_at_most_one_pending_req(msg, cr.object_ref()))))), simple_reconciler(), input, next_and_invariant, continue_reconcile(simple_reconciler()), pre, post);
}

proof fn lemma_exists_resp_msg_sent_and_after_get_cr_pc_leads_to_after_create_cm_pc(req_msg: Message, cr: CustomResourceView)
    ensures
        sm_spec(simple_reconciler()).entails(
            lift_state(|s: State<SimpleReconcileState>| {
                exists |m: Message| {
                    &&& #[trigger] s.message_in_flight(m)
                    &&& resp_msg_matches_req_msg(m, req_msg)
                }
            }).and(lift_state(reconciler_at_after_get_cr_pc_and_pending_req(req_msg, cr)))
            .leads_to(lift_state(reconciler_at_after_create_cm_pc(cr)))
        ),
{
    let m_to_pre1 = |m: Message| lift_state(|s: State<SimpleReconcileState>| {
        &&& s.message_in_flight(m)
        &&& resp_msg_matches_req_msg(m, req_msg)
    });
    let pre2 = lift_state(reconciler_at_after_get_cr_pc_and_pending_req(req_msg, cr));
    let post = lift_state(reconciler_at_after_create_cm_pc(cr));
    assert forall |msg: Message| #[trigger] sm_spec(simple_reconciler()).entails(m_to_pre1(msg).and(pre2).leads_to(post)) by {
        lemma_resp_msg_sent_and_after_get_cr_pc_leads_to_after_create_cm_pc(msg, req_msg, cr);
        let pre = lift_state(|s: State<SimpleReconcileState>| {
            &&& s.message_in_flight(msg)
            &&& resp_msg_matches_req_msg(msg, req_msg)
            &&& reconciler_at_after_get_cr_pc_and_pending_req(req_msg, cr)(s)
        });
        temp_pred_equality::<State<SimpleReconcileState>>(pre, m_to_pre1(msg).and(pre2));
    };
    leads_to_exists_intro::<State<SimpleReconcileState>, Message>(sm_spec(simple_reconciler()), |m| m_to_pre1(m).and(pre2), post);
    tla_exists_and_equality::<State<SimpleReconcileState>, Message>(m_to_pre1, pre2);

    // This is very tedious proof to show exists_m_to_pre1 == tla_exists(m_to_pre1)
    // I hope we can encapsulate this as a lemma
    let exists_m_to_pre1 = lift_state(|s: State<SimpleReconcileState>| {
        exists |m: Message| {
            &&& #[trigger] s.message_in_flight(m)
            &&& resp_msg_matches_req_msg(m, req_msg)
        }
    });
    assert forall |ex| #[trigger] exists_m_to_pre1.satisfied_by(ex) implies tla_exists(m_to_pre1).satisfied_by(ex) by {
        let m = choose |m: Message| {
            &&& #[trigger] ex.head().message_in_flight(m)
            &&& resp_msg_matches_req_msg(m, req_msg)
        };
        assert(m_to_pre1(m).satisfied_by(ex));
    };
    temp_pred_equality::<State<SimpleReconcileState>>(exists_m_to_pre1, tla_exists(m_to_pre1));
}

proof fn lemma_exists_resp_msg_sent_and_after_get_cr_pc_leads_to_after_create_cm_pc_with_invariant(req_msg: Message, cr: CustomResourceView)
    ensures
    sm_partial_spec(simple_reconciler()).and(tla_forall(|msg| always(lift_state(controller_runtime_safety::resp_matches_at_most_one_pending_req(msg, cr.object_ref()))))).entails(
            lift_state(|s: State<SimpleReconcileState>| {
                exists |m: Message| {
                    &&& #[trigger] s.message_in_flight(m)
                    &&& resp_msg_matches_req_msg(m, req_msg)
                }
            }).and(lift_state(reconciler_at_after_get_cr_pc_and_pending_req(req_msg, cr)))
            .leads_to(lift_state(reconciler_at_after_create_cm_pc(cr)))
        ),
{
    let m_to_pre1 = |m: Message| lift_state(|s: State<SimpleReconcileState>| {
        &&& s.message_in_flight(m)
        &&& resp_msg_matches_req_msg(m, req_msg)
    });
    let pre2 = lift_state(reconciler_at_after_get_cr_pc_and_pending_req(req_msg, cr));
    let post = lift_state(reconciler_at_after_create_cm_pc(cr));
    assert forall |msg: Message| sm_partial_spec(simple_reconciler()).and(tla_forall(|msg1| always(lift_state(controller_runtime_safety::resp_matches_at_most_one_pending_req(msg1, cr.object_ref()))))).entails(#[trigger] m_to_pre1(msg).and(pre2).leads_to(post)) by {
        lemma_resp_msg_sent_and_after_get_cr_pc_leads_to_after_create_cm_pc_with_invariant(msg, req_msg, cr);
        let pre = lift_state(|s: State<SimpleReconcileState>| {
            &&& s.message_in_flight(msg)
            &&& resp_msg_matches_req_msg(msg, req_msg)
            &&& reconciler_at_after_get_cr_pc_and_pending_req(req_msg, cr)(s)
        });
        temp_pred_equality::<State<SimpleReconcileState>>(pre, m_to_pre1(msg).and(pre2));
    };
    leads_to_exists_intro::<State<SimpleReconcileState>, Message>(sm_partial_spec(simple_reconciler()).and(tla_forall(|msg1| always(lift_state(controller_runtime_safety::resp_matches_at_most_one_pending_req(msg1, cr.object_ref()))))), |m| m_to_pre1(m).and(pre2), post);
    tla_exists_and_equality::<State<SimpleReconcileState>, Message>(m_to_pre1, pre2);

    // This is very tedious proof to show exists_m_to_pre1 == tla_exists(m_to_pre1)
    // I hope we can encapsulate this as a lemma
    let exists_m_to_pre1 = lift_state(|s: State<SimpleReconcileState>| {
        exists |m: Message| {
            &&& #[trigger] s.message_in_flight(m)
            &&& resp_msg_matches_req_msg(m, req_msg)
        }
    });
    assert forall |ex| #[trigger] exists_m_to_pre1.satisfied_by(ex) implies tla_exists(m_to_pre1).satisfied_by(ex) by {
        let m = choose |m: Message| {
            &&& #[trigger] ex.head().message_in_flight(m)
            &&& resp_msg_matches_req_msg(m, req_msg)
        };
        assert(m_to_pre1(m).satisfied_by(ex));
    };
    temp_pred_equality::<State<SimpleReconcileState>>(exists_m_to_pre1, tla_exists(m_to_pre1));
}

}
