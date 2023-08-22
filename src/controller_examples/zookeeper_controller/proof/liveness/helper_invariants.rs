// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::{
    api_method::*, common::*, error::*, resource::*, stateful_set::*,
};
use crate::kubernetes_cluster::spec::{
    cluster::*,
    cluster_state_machine::Step,
    controller::common::{controller_req_msg, ControllerActionInput, ControllerStep},
    message::*,
};
use crate::pervasive_ext::multiset_lemmas;
use crate::reconciler::spec::reconciler::*;
use crate::temporal_logic::{defs::*, rules::*};
use crate::zookeeper_controller::{
    common::*,
    proof::common::*,
    spec::{reconciler::*, zookeepercluster::*},
};
use vstd::{multiset::*, prelude::*};

verus! {

pub open spec fn sts_create_request_msg(key: ObjectRef) -> FnSpec(Message) -> bool {
    |msg: Message|
        msg.dst.is_KubernetesAPI()
        && msg.content.is_create_request()
        && msg.content.get_create_request().namespace == make_stateful_set_key(key).namespace
        && msg.content.get_create_request().obj.metadata.name.get_Some_0() == make_stateful_set_key(key).name
        && msg.content.get_create_request().obj.kind == make_stateful_set_key(key).kind
}

pub open spec fn sts_create_request_msg_since(key: ObjectRef, rest_id: RestId) -> FnSpec(Message) -> bool {
    |msg: Message|
        sts_create_request_msg(key)(msg)
        && msg.content.get_rest_id() >= rest_id
}

pub open spec fn pending_msg_at_after_create_stateful_set_step_is_create_sts_req(
    key: ObjectRef
) -> StatePred<ZKCluster>
    recommends
        key.kind.is_CustomResourceKind(),
{
    |s: ZKCluster| {
        at_zookeeper_step(key, ZookeeperReconcileStep::AfterCreateStatefulSet)(s)
            ==> {
                &&& ZKCluster::pending_k8s_api_req_msg(s, key)
                &&& sts_create_request_msg(key)(s.pending_req_of(key))
            }
    }
}

pub proof fn lemma_always_pending_msg_at_after_create_stateful_set_step_is_create_sts_req(
    spec: TempPred<ZKCluster>, key: ObjectRef
)
    requires
        spec.entails(lift_state(ZKCluster::init())),
        spec.entails(always(lift_action(ZKCluster::next()))),
    ensures
        spec.entails(
            always(lift_state(pending_msg_at_after_create_stateful_set_step_is_create_sts_req(key)))
        ),
{
    let invariant = pending_msg_at_after_create_stateful_set_step_is_create_sts_req(key);
    let init = ZKCluster::init();
    let stronger_next = |s, s_prime| {
        &&& ZKCluster::next()(s, s_prime)
        &&& ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
    };

    ZKCluster::lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec);

    entails_always_and_n!(
        spec,
        lift_action(ZKCluster::next()),
        lift_state(ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata())
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(ZKCluster::next())
        .and(lift_state(ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()))
    );

    init_invariant(spec, init, stronger_next, invariant);
}

pub open spec fn filtered_create_sts_req_len_is_at_most_one(
    key: ObjectRef, rest_id: RestId
) -> StatePred<ZKCluster>
    recommends
        key.kind.is_CustomResourceKind(),
{
    |s: ZKCluster| {
        s.network_state.in_flight.filter(sts_create_request_msg_since(key, rest_id)).len() > 0
        ==> {
            &&& at_zookeeper_step(key, ZookeeperReconcileStep::AfterCreateStatefulSet)(s)
            &&& s.pending_req_of(key).content.get_rest_id() >= rest_id
            &&& s.message_in_flight(s.pending_req_of(key))
            &&& sts_create_request_msg_since(key, rest_id)(s.pending_req_of(key))
            &&& s.network_state.in_flight.filter(sts_create_request_msg_since(key, rest_id)).len() == 1
        }
    }
}

proof fn lemma_always_filtered_create_sts_req_len_is_at_most_one(
    spec: TempPred<ZKCluster>, key: ObjectRef, rest_id: RestId
)
    requires
        spec.entails(lift_state(ZKCluster::rest_id_counter_is(rest_id))),
        spec.entails(lift_state(ZKCluster::every_in_flight_msg_has_lower_id_than_allocator())),
        spec.entails(lift_state(pending_msg_at_after_create_stateful_set_step_is_create_sts_req(key))),
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(always(lift_state(ZKCluster::crash_disabled()))),
        spec.entails(always(lift_state(ZKCluster::busy_disabled()))),
        spec.entails(always(lift_state(pending_msg_at_after_create_stateful_set_step_is_create_sts_req(key)))),
        spec.entails(always(lift_state(ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(ZKCluster::rest_id_counter_is_no_smaller_than(rest_id)))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_msg_has_unique_id()))),
        key.kind.is_CustomResourceKind(),
    ensures
        spec.entails(
            always(lift_state(filtered_create_sts_req_len_is_at_most_one(key, rest_id)))
        ),
{
    let init = |s: ZKCluster| {
        &&& ZKCluster::rest_id_counter_is(rest_id)(s)
        &&& ZKCluster::every_in_flight_msg_has_lower_id_than_allocator()(s)
        &&& pending_msg_at_after_create_stateful_set_step_is_create_sts_req(key)(s)
    };
    let stronger_next = |s, s_prime: ZKCluster| {
        &&& ZKCluster::next()(s, s_prime)
        &&& ZKCluster::crash_disabled()(s)
        &&& ZKCluster::busy_disabled()(s)
        &&& pending_msg_at_after_create_stateful_set_step_is_create_sts_req(key)(s)
        &&& ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
        &&& ZKCluster::rest_id_counter_is_no_smaller_than(rest_id)(s)
        &&& ZKCluster::every_in_flight_msg_has_unique_id()(s)
    };
    let invariant = filtered_create_sts_req_len_is_at_most_one(key, rest_id);

    entails_and_n!(
        spec,
        lift_state(ZKCluster::rest_id_counter_is(rest_id)),
        lift_state(ZKCluster::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(pending_msg_at_after_create_stateful_set_step_is_create_sts_req(key))
    );
    temp_pred_equality(
        lift_state(init),
        lift_state(ZKCluster::rest_id_counter_is(rest_id))
        .and(lift_state(ZKCluster::every_in_flight_msg_has_lower_id_than_allocator()))
        .and(lift_state(pending_msg_at_after_create_stateful_set_step_is_create_sts_req(key)))
    );

    entails_always_and_n!(
        spec,
        lift_action(ZKCluster::next()),
        lift_state(ZKCluster::crash_disabled()),
        lift_state(ZKCluster::busy_disabled()),
        lift_state(pending_msg_at_after_create_stateful_set_step_is_create_sts_req(key)),
        lift_state(ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        lift_state(ZKCluster::rest_id_counter_is_no_smaller_than(rest_id)),
        lift_state(ZKCluster::every_in_flight_msg_has_unique_id())
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(ZKCluster::next())
        .and(lift_state(ZKCluster::crash_disabled()))
        .and(lift_state(ZKCluster::busy_disabled()))
        .and(lift_state(pending_msg_at_after_create_stateful_set_step_is_create_sts_req(key)))
        .and(lift_state(ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()))
        .and(lift_state(ZKCluster::rest_id_counter_is_no_smaller_than(rest_id)))
        .and(lift_state(ZKCluster::every_in_flight_msg_has_unique_id()))
    );

    assert forall |s: ZKCluster| #[trigger] init(s) implies invariant(s) by {
        let sts_create_req_multiset = s.network_state.in_flight.filter(sts_create_request_msg_since(key, rest_id));

        assert forall |msg| sts_create_req_multiset.count(msg) == 0 by {
            assert(!(s.message_in_flight(msg) && sts_create_request_msg_since(key, rest_id)(msg)));
        }
        multiset_lemmas::len_is_zero_means_count_for_each_value_is_zero(sts_create_req_multiset);
    }

    assert forall |s, s_prime: ZKCluster| invariant(s) && #[trigger] stronger_next(s, s_prime)
    implies invariant(s_prime) by {
        let sts_create_req_multiset = s.network_state.in_flight.filter(sts_create_request_msg_since(key, rest_id));
        let sts_create_req_multiset_prime = s_prime.network_state.in_flight.filter(sts_create_request_msg_since(key, rest_id));
        let step = choose |step| ZKCluster::next_step(s, s_prime, step);
        match step {
            Step::KubernetesAPIStep(input) => {
                if !at_zookeeper_step(key, ZookeeperReconcileStep::AfterCreateStatefulSet)(s) {
                    // If not at AfterUpdateStatefulSet step,
                    // due to inductive hypothesis, the set of messages remains unchanged (len() = 0)
                    // between s and s_prime.
                    assert(sts_create_req_multiset =~= sts_create_req_multiset_prime);
                } else {
                    // If at AfterUpdateStatefulSet step,
                    // we need to split the case.
                    let chosen_msg = input.get_Some_0();
                    if sts_create_request_msg_since(key, rest_id)(chosen_msg) {
                        // If the chosen message to handle is the one that creates StatefulSet,
                        // then the message set shrinks by one.
                        assert(sts_create_req_multiset.remove(chosen_msg) =~= sts_create_req_multiset_prime);
                    } else {
                        // Otherwise the set remains unchanged.
                        assert(sts_create_req_multiset =~= sts_create_req_multiset_prime);
                    }
                }
            },
            Step::ControllerStep(input) => {
                let chosen_key = input.1.get_Some_0();
                if chosen_key == key {
                    // If the state machine chooses the reconciler for our key to take the next transition...
                    if at_zookeeper_step(key, ZookeeperReconcileStep::AfterCreateStatefulSet)(s_prime) {
                        // If transition to AfterUpdateStatefulSet step,
                        // then there must be a StatefulSet create request message just sent to the network.
                        // And thanks to rest_id_counter_is_no_smaller_than, we know that the newly sent request
                        // has a no-smaller id than rest_id.
                        // So We go ahead and prove s.network_state.in_flight.filter(sts_create_request_msg_since(key, rest_id)).len() == 1
                        // using extensional equality here.
                        assert(sts_create_req_multiset.insert(s_prime.pending_req_of(key)) =~= sts_create_req_multiset_prime);
                    } else if at_zookeeper_step(key, ZookeeperReconcileStep::Done)(s_prime) {
                        if at_zookeeper_step(key, ZookeeperReconcileStep::AfterCreateStatefulSet)(s) {
                            if s.pending_req_of(key).content.get_rest_id() >= rest_id {
                                // This is the most tricky path: we need to show
                                // s.network_state.in_flight.filter(sts_create_request_msg_since(key, rest_id)).len() == 0
                                // since this transition won't remove any req_msg from the network.
                                // The reasoning is that the transition can only happen
                                // if the response message is in the network,
                                // which shares the same rest_id with the request message.
                                // Thanks to every_in_flight_msg_has_unique_id(), we know that
                                // if the response message is in the network, then the request message is not,
                                // which means s.network_state.in_flight.filter(sts_create_request_msg_since(key, rest_id)).len() == 0
                                // has to be true (due to inductive hypothesis).
                                assert(sts_create_req_multiset =~= sts_create_req_multiset_prime);
                            } else {
                                assert(sts_create_req_multiset =~= sts_create_req_multiset_prime);
                            }
                        } else {
                            assert(sts_create_req_multiset =~= sts_create_req_multiset_prime);
                        }
                    } else {
                        assert(sts_create_req_multiset =~= sts_create_req_multiset_prime);
                    }
                } else {
                    // If the state machine chooses the reconciler for a different key to take the next transition...
                    // It is trivial because of the isolation between different reconcilers:
                    // each reconciler does not touch other reconcilers' resources.
                    // The isolation property comes from the way each reconciler names its owned resources.
                    // Note that here we implicitly use each_object_in_reconcile_has_consistent_key_and_valid_metadata
                    // because the reconciler uses zk, instead of the key of zk, when naming the resources.
                    assert(sts_create_req_multiset =~= sts_create_req_multiset_prime);
                }
            },
            Step::ClientStep(input) => {
                assert(sts_create_req_multiset =~= sts_create_req_multiset_prime);
            },
            _ => {
            }
        }
    }

    init_invariant(spec, init, stronger_next, invariant);
}

pub open spec fn at_most_one_create_sts_req_since_rest_id_is_in_flight(
    key: ObjectRef, rest_id: RestId
) -> StatePred<ZKCluster>
    recommends
        key.kind.is_CustomResourceKind(),
{
    |s: ZKCluster| {
        forall |msg| {
            &&& #[trigger] s.network_state.in_flight.contains(msg)
            &&& sts_create_request_msg_since(key, rest_id)(msg)
        } ==> {
            let pending_msg = s.pending_req_of(key);
            &&& at_zookeeper_step(key, ZookeeperReconcileStep::AfterCreateStatefulSet)(s)
            &&& pending_msg.content.get_rest_id() >= rest_id
            &&& msg == pending_msg
            &&& s.network_state.in_flight.count(msg) == 1
        }
    }
}

pub proof fn lemma_always_at_most_one_create_sts_req_since_rest_id_is_in_flight(
    spec: TempPred<ZKCluster>, key: ObjectRef, rest_id: RestId
)
    requires
        spec.entails(lift_state(ZKCluster::rest_id_counter_is(rest_id))),
        spec.entails(lift_state(ZKCluster::every_in_flight_msg_has_lower_id_than_allocator())),
        spec.entails(lift_state(pending_msg_at_after_create_stateful_set_step_is_create_sts_req(key))),
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(always(lift_state(ZKCluster::crash_disabled()))),
        spec.entails(always(lift_state(ZKCluster::busy_disabled()))),
        spec.entails(always(lift_state(pending_msg_at_after_create_stateful_set_step_is_create_sts_req(key)))),
        spec.entails(always(lift_state(ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(ZKCluster::rest_id_counter_is_no_smaller_than(rest_id)))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_msg_has_unique_id()))),
        key.kind.is_CustomResourceKind(),
    ensures
        spec.entails(
            always(lift_state(at_most_one_create_sts_req_since_rest_id_is_in_flight(key, rest_id)))
        ),
{
    lemma_always_filtered_create_sts_req_len_is_at_most_one(spec, key, rest_id);

    let p = lift_state(at_most_one_create_sts_req_since_rest_id_is_in_flight(key, rest_id));
    let q = lift_state(filtered_create_sts_req_len_is_at_most_one(key, rest_id));

    assert_by(
        p == q, {
            assert forall |ex| p.satisfied_by(ex) implies q.satisfied_by(ex) by {
                multiset_lemmas::filtered_size_is_zero_means_no_such_value(
                    ex.head().network_state.in_flight, sts_create_request_msg_since(key, rest_id)
                );
                multiset_lemmas::filtered_size_is_one_means_only_one_such_value(
                    ex.head().network_state.in_flight, sts_create_request_msg_since(key, rest_id)
                );
            }

            assert forall |ex| q.satisfied_by(ex) implies p.satisfied_by(ex) by {
                multiset_lemmas::filtered_size_is_zero_means_no_such_value(
                    ex.head().network_state.in_flight, sts_create_request_msg_since(key, rest_id)
                );
                multiset_lemmas::filtered_size_is_one_means_only_one_such_value(
                    ex.head().network_state.in_flight, sts_create_request_msg_since(key, rest_id)
                );
            }

            temp_pred_equality(p, q);
        }
    );
}

pub open spec fn sts_update_request_msg(key: ObjectRef) -> FnSpec(Message) -> bool {
    |msg: Message|
        msg.dst.is_KubernetesAPI()
        && msg.content.is_update_request()
        && msg.content.get_update_request().key == make_stateful_set_key(key)
}

pub open spec fn sts_update_request_msg_since(key: ObjectRef, rest_id: RestId) -> FnSpec(Message) -> bool {
    |msg: Message|
        sts_update_request_msg(key)(msg)
        && msg.content.get_rest_id() >= rest_id
}

pub open spec fn pending_msg_at_after_update_stateful_set_step_is_update_sts_req(
    key: ObjectRef
) -> StatePred<ZKCluster>
    recommends
        key.kind.is_CustomResourceKind(),
{
    |s: ZKCluster| {
        at_zookeeper_step(key, ZookeeperReconcileStep::AfterUpdateStatefulSet)(s)
            ==> {
                &&& ZKCluster::pending_k8s_api_req_msg(s, key)
                &&& sts_update_request_msg(key)(s.pending_req_of(key))
            }
    }
}

pub proof fn lemma_always_pending_msg_at_after_update_stateful_set_step_is_update_sts_req(
    spec: TempPred<ZKCluster>, key: ObjectRef
)
    requires
        spec.entails(lift_state(ZKCluster::init())),
        spec.entails(always(lift_action(ZKCluster::next()))),
    ensures
        spec.entails(
            always(lift_state(pending_msg_at_after_update_stateful_set_step_is_update_sts_req(key)))
        ),
{
    let invariant = pending_msg_at_after_update_stateful_set_step_is_update_sts_req(key);
    let init = ZKCluster::init();
    let stronger_next = |s, s_prime| {
        &&& ZKCluster::next()(s, s_prime)
        &&& ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
    };

    ZKCluster::lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec);

    entails_always_and_n!(
        spec,
        lift_action(ZKCluster::next()),
        lift_state(ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata())
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(ZKCluster::next())
        .and(lift_state(ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()))
    );

    init_invariant(spec, init, stronger_next, invariant);
}

pub open spec fn filtered_update_sts_req_len_is_at_most_one(
    key: ObjectRef, rest_id: RestId
) -> StatePred<ZKCluster>
    recommends
        key.kind.is_CustomResourceKind(),
{
    |s: ZKCluster| {
        s.network_state.in_flight.filter(sts_update_request_msg_since(key, rest_id)).len() > 0
        ==> {
            &&& at_zookeeper_step(key, ZookeeperReconcileStep::AfterUpdateStatefulSet)(s)
            &&& s.pending_req_of(key).content.get_rest_id() >= rest_id
            &&& s.message_in_flight(s.pending_req_of(key))
            &&& sts_update_request_msg_since(key, rest_id)(s.pending_req_of(key))
            &&& s.network_state.in_flight.filter(sts_update_request_msg_since(key, rest_id)).len() == 1
        }
    }
}

proof fn lemma_always_filtered_update_sts_req_len_is_at_most_one(
    spec: TempPred<ZKCluster>, key: ObjectRef, rest_id: RestId
)
    requires
        spec.entails(lift_state(ZKCluster::rest_id_counter_is(rest_id))),
        spec.entails(lift_state(ZKCluster::every_in_flight_msg_has_lower_id_than_allocator())),
        spec.entails(lift_state(pending_msg_at_after_update_stateful_set_step_is_update_sts_req(key))),
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(always(lift_state(ZKCluster::crash_disabled()))),
        spec.entails(always(lift_state(ZKCluster::busy_disabled()))),
        spec.entails(always(lift_state(pending_msg_at_after_update_stateful_set_step_is_update_sts_req(key)))),
        spec.entails(always(lift_state(ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(ZKCluster::rest_id_counter_is_no_smaller_than(rest_id)))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_msg_has_unique_id()))),
        key.kind.is_CustomResourceKind(),
    ensures
        spec.entails(
            always(lift_state(filtered_update_sts_req_len_is_at_most_one(key, rest_id)))
        ),
{
    let init = |s: ZKCluster| {
        &&& ZKCluster::rest_id_counter_is(rest_id)(s)
        &&& ZKCluster::every_in_flight_msg_has_lower_id_than_allocator()(s)
        &&& pending_msg_at_after_update_stateful_set_step_is_update_sts_req(key)(s)
    };
    let stronger_next = |s, s_prime: ZKCluster| {
        &&& ZKCluster::next()(s, s_prime)
        &&& ZKCluster::crash_disabled()(s)
        &&& ZKCluster::busy_disabled()(s)
        &&& pending_msg_at_after_update_stateful_set_step_is_update_sts_req(key)(s)
        &&& ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
        &&& ZKCluster::rest_id_counter_is_no_smaller_than(rest_id)(s)
        &&& ZKCluster::every_in_flight_msg_has_unique_id()(s)
    };
    let invariant = filtered_update_sts_req_len_is_at_most_one(key, rest_id);

    entails_and_n!(
        spec,
        lift_state(ZKCluster::rest_id_counter_is(rest_id)),
        lift_state(ZKCluster::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(pending_msg_at_after_update_stateful_set_step_is_update_sts_req(key))
    );
    temp_pred_equality(
        lift_state(init),
        lift_state(ZKCluster::rest_id_counter_is(rest_id))
        .and(lift_state(ZKCluster::every_in_flight_msg_has_lower_id_than_allocator()))
        .and(lift_state(pending_msg_at_after_update_stateful_set_step_is_update_sts_req(key)))
    );

    entails_always_and_n!(
        spec,
        lift_action(ZKCluster::next()),
        lift_state(ZKCluster::crash_disabled()),
        lift_state(ZKCluster::busy_disabled()),
        lift_state(pending_msg_at_after_update_stateful_set_step_is_update_sts_req(key)),
        lift_state(ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        lift_state(ZKCluster::rest_id_counter_is_no_smaller_than(rest_id)),
        lift_state(ZKCluster::every_in_flight_msg_has_unique_id())
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(ZKCluster::next())
        .and(lift_state(ZKCluster::crash_disabled()))
        .and(lift_state(ZKCluster::busy_disabled()))
        .and(lift_state(pending_msg_at_after_update_stateful_set_step_is_update_sts_req(key)))
        .and(lift_state(ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()))
        .and(lift_state(ZKCluster::rest_id_counter_is_no_smaller_than(rest_id)))
        .and(lift_state(ZKCluster::every_in_flight_msg_has_unique_id()))
    );

    assert forall |s: ZKCluster| #[trigger] init(s) implies invariant(s) by {
        let sts_update_req_multiset = s.network_state.in_flight.filter(sts_update_request_msg_since(key, rest_id));

        assert forall |msg| sts_update_req_multiset.count(msg) == 0 by {
            assert(!(s.message_in_flight(msg) && sts_update_request_msg_since(key, rest_id)(msg)));
        }
        multiset_lemmas::len_is_zero_means_count_for_each_value_is_zero(sts_update_req_multiset);
    }

    assert forall |s, s_prime: ZKCluster| invariant(s) && #[trigger] stronger_next(s, s_prime)
    implies invariant(s_prime) by {
        let sts_update_req_multiset = s.network_state.in_flight.filter(sts_update_request_msg_since(key, rest_id));
        let sts_update_req_multiset_prime = s_prime.network_state.in_flight.filter(sts_update_request_msg_since(key, rest_id));
        let step = choose |step| ZKCluster::next_step(s, s_prime, step);
        match step {
            Step::KubernetesAPIStep(input) => {
                if !at_zookeeper_step(key, ZookeeperReconcileStep::AfterUpdateStatefulSet)(s) {
                    // If not at AfterUpdateStatefulSet step,
                    // due to inductive hypothesis, the set of messages remains unchanged (len() = 0)
                    // between s and s_prime.
                    assert(sts_update_req_multiset =~= sts_update_req_multiset_prime);
                } else {
                    // If at AfterUpdateStatefulSet step,
                    // we need to split the case.
                    let chosen_msg = input.get_Some_0();
                    if sts_update_request_msg_since(key, rest_id)(chosen_msg) {
                        // If the chosen message to handle is the one that updates StatefulSet,
                        // then the message set shrinks by one.
                        assert(sts_update_req_multiset.remove(chosen_msg) =~= sts_update_req_multiset_prime);
                    } else {
                        // Otherwise the set remains unchanged.
                        assert(sts_update_req_multiset =~= sts_update_req_multiset_prime);
                    }
                }
            },
            Step::ControllerStep(input) => {
                let chosen_key = input.1.get_Some_0();
                if chosen_key == key {
                    // If the state machine chooses the reconciler for our key to take the next transition...
                    if at_zookeeper_step(key, ZookeeperReconcileStep::AfterUpdateStatefulSet)(s_prime) {
                        // If transition to AfterUpdateStatefulSet step,
                        // then there must be a StatefulSet update request message just sent to the network.
                        // And thanks to rest_id_counter_is_no_smaller_than, we know that the newly sent request
                        // has a no-smaller id than rest_id.
                        // So We go ahead and prove s.network_state.in_flight.filter(sts_update_request_msg_since(key, rest_id)).len() == 1
                        // using extensional equality here.
                        assert(sts_update_req_multiset.insert(s_prime.pending_req_of(key)) =~= sts_update_req_multiset_prime);
                    } else if at_zookeeper_step(key, ZookeeperReconcileStep::Done)(s_prime) {
                        if at_zookeeper_step(key, ZookeeperReconcileStep::AfterUpdateStatefulSet)(s) {
                            if s.pending_req_of(key).content.get_rest_id() >= rest_id {
                                // This is the most tricky path: we need to show
                                // s.network_state.in_flight.filter(sts_update_request_msg_since(key, rest_id)).len() == 0
                                // since this transition won't remove any req_msg from the network.
                                // The reasoning is that the transition can only happen
                                // if the response message is in the network,
                                // which shares the same rest_id with the request message.
                                // Thanks to every_in_flight_msg_has_unique_id(), we know that
                                // if the response message is in the network, then the request message is not,
                                // which means s.network_state.in_flight.filter(sts_update_request_msg_since(key, rest_id)).len() == 0
                                // has to be true (due to inductive hypothesis).
                                assert(sts_update_req_multiset =~= sts_update_req_multiset_prime);
                            } else {
                                assert(sts_update_req_multiset =~= sts_update_req_multiset_prime);
                            }
                        } else {
                            assert(sts_update_req_multiset =~= sts_update_req_multiset_prime);
                        }
                    } else {
                        assert(sts_update_req_multiset =~= sts_update_req_multiset_prime);
                    }
                } else {
                    // If the state machine chooses the reconciler for a different key to take the next transition...
                    // It is trivial because of the isolation between different reconcilers:
                    // each reconciler does not touch other reconcilers' resources.
                    // The isolation property comes from the way each reconciler names its owned resources.
                    // Note that here we implicitly use each_object_in_reconcile_has_consistent_key_and_valid_metadata
                    // because the reconciler uses zk, instead of the key of zk, when naming the resources.
                    assert(sts_update_req_multiset =~= sts_update_req_multiset_prime);
                }
            },
            Step::ClientStep(input) => {
                assert(sts_update_req_multiset =~= sts_update_req_multiset_prime);
            },
            _ => {
            }
        }
    }

    init_invariant(spec, init, stronger_next, invariant);
}

pub open spec fn at_most_one_update_sts_req_since_rest_id_is_in_flight(
    key: ObjectRef, rest_id: RestId
) -> StatePred<ZKCluster>
    recommends
        key.kind.is_CustomResourceKind(),
{
    |s: ZKCluster| {
        forall |msg| {
            &&& #[trigger] s.network_state.in_flight.contains(msg)
            &&& sts_update_request_msg_since(key, rest_id)(msg)
        } ==> {
            let pending_msg = s.pending_req_of(key);
            &&& at_zookeeper_step(key, ZookeeperReconcileStep::AfterUpdateStatefulSet)(s)
            &&& pending_msg.content.get_rest_id() >= rest_id
            &&& msg == pending_msg
            &&& s.network_state.in_flight.count(msg) == 1
        }
    }
}

pub proof fn lemma_always_at_most_one_update_sts_req_since_rest_id_is_in_flight(
    spec: TempPred<ZKCluster>, key: ObjectRef, rest_id: RestId
)
    requires
        spec.entails(lift_state(ZKCluster::rest_id_counter_is(rest_id))),
        spec.entails(lift_state(ZKCluster::every_in_flight_msg_has_lower_id_than_allocator())),
        spec.entails(lift_state(pending_msg_at_after_update_stateful_set_step_is_update_sts_req(key))),
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(always(lift_state(ZKCluster::crash_disabled()))),
        spec.entails(always(lift_state(ZKCluster::busy_disabled()))),
        spec.entails(always(lift_state(pending_msg_at_after_update_stateful_set_step_is_update_sts_req(key)))),
        spec.entails(always(lift_state(ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(ZKCluster::rest_id_counter_is_no_smaller_than(rest_id)))),
        spec.entails(always(lift_state(ZKCluster::every_in_flight_msg_has_unique_id()))),
        key.kind.is_CustomResourceKind(),
    ensures
        spec.entails(
            always(lift_state(at_most_one_update_sts_req_since_rest_id_is_in_flight(key, rest_id)))
        ),
{
    lemma_always_filtered_update_sts_req_len_is_at_most_one(spec, key, rest_id);

    let p = lift_state(at_most_one_update_sts_req_since_rest_id_is_in_flight(key, rest_id));
    let q = lift_state(filtered_update_sts_req_len_is_at_most_one(key, rest_id));

    assert_by(
        p == q, {
            assert forall |ex| p.satisfied_by(ex) implies q.satisfied_by(ex) by {
                multiset_lemmas::filtered_size_is_zero_means_no_such_value(
                    ex.head().network_state.in_flight, sts_update_request_msg_since(key, rest_id)
                );
                multiset_lemmas::filtered_size_is_one_means_only_one_such_value(
                    ex.head().network_state.in_flight, sts_update_request_msg_since(key, rest_id)
                );
            }

            assert forall |ex| q.satisfied_by(ex) implies p.satisfied_by(ex) by {
                multiset_lemmas::filtered_size_is_zero_means_no_such_value(
                    ex.head().network_state.in_flight, sts_update_request_msg_since(key, rest_id)
                );
                multiset_lemmas::filtered_size_is_one_means_only_one_such_value(
                    ex.head().network_state.in_flight, sts_update_request_msg_since(key, rest_id)
                );
            }

            temp_pred_equality(p, q);
        }
    );
}

pub open spec fn every_update_sts_req_since_rest_id_does_the_same(
    zk: ZookeeperClusterView, rest_id: RestId
) -> StatePred<ZKCluster>
    recommends
        zk.well_formed(),
{
    |s: ZKCluster| {
        forall |msg: Message| {
            &&& #[trigger] s.network_state.in_flight.contains(msg)
            &&& sts_update_request_msg_since(zk.object_ref(), rest_id)(msg)
        } ==> msg.content.get_update_request().obj.spec == StatefulSetView::marshal_spec(make_stateful_set(zk).spec)
    }
}

pub proof fn lemma_always_every_update_sts_req_since_rest_id_does_the_same(
    spec: TempPred<ZKCluster>, zk: ZookeeperClusterView, rest_id: RestId
)
    requires
        spec.entails(lift_state(ZKCluster::rest_id_counter_is(rest_id))),
        spec.entails(lift_state(ZKCluster::every_in_flight_msg_has_lower_id_than_allocator())),
        spec.entails(always(lift_action(ZKCluster::next()))),
        spec.entails(always(lift_state(ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()))),
        spec.entails(always(lift_state(ZKCluster::rest_id_counter_is_no_smaller_than(rest_id)))),
        spec.entails(always(lift_state(ZKCluster::the_object_in_reconcile_has_spec_and_uid_as(zk)))),
    ensures
        spec.entails(always(lift_state(every_update_sts_req_since_rest_id_does_the_same(zk, rest_id)))),
{
    let init = |s: ZKCluster| {
        &&& ZKCluster::rest_id_counter_is(rest_id)(s)
        &&& ZKCluster::every_in_flight_msg_has_lower_id_than_allocator()(s)
    };
    let stronger_next = |s, s_prime: ZKCluster| {
        &&& ZKCluster::next()(s, s_prime)
        &&& ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
        &&& ZKCluster::rest_id_counter_is_no_smaller_than(rest_id)(s)
        &&& ZKCluster::the_object_in_reconcile_has_spec_and_uid_as(zk)(s)
    };
    let invariant = every_update_sts_req_since_rest_id_does_the_same(zk, rest_id);

    entails_and_n!(
        spec,
        lift_state(ZKCluster::rest_id_counter_is(rest_id)),
        lift_state(ZKCluster::every_in_flight_msg_has_lower_id_than_allocator())
    );
    temp_pred_equality(
        lift_state(init),
        lift_state(ZKCluster::rest_id_counter_is(rest_id))
        .and(lift_state(ZKCluster::every_in_flight_msg_has_lower_id_than_allocator()))
    );

    entails_always_and_n!(
        spec,
        lift_action(ZKCluster::next()),
        lift_state(ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        lift_state(ZKCluster::rest_id_counter_is_no_smaller_than(rest_id)),
        lift_state(ZKCluster::the_object_in_reconcile_has_spec_and_uid_as(zk))
    );
    temp_pred_equality(
        lift_action(stronger_next),
        lift_action(ZKCluster::next())
        .and(lift_state(ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()))
        .and(lift_state(ZKCluster::rest_id_counter_is_no_smaller_than(rest_id)))
        .and(lift_state(ZKCluster::the_object_in_reconcile_has_spec_and_uid_as(zk)))
    );

    assert forall |s, s_prime: ZKCluster| invariant(s) && #[trigger] stronger_next(s, s_prime)
    implies invariant(s_prime) by {
        assert forall |msg: Message|
            #[trigger] s_prime.network_state.in_flight.contains(msg)
            && sts_update_request_msg_since(zk.object_ref(), rest_id)(msg)
        implies msg.content.get_update_request().obj.spec == StatefulSetView::marshal_spec(make_stateful_set(zk).spec) by {
            if s.network_state.in_flight.contains(msg) {} else {}
        }
    }

    init_invariant(spec, init, stronger_next, invariant);
}

pub open spec fn sts_delete_request_msg(key: ObjectRef) -> FnSpec(Message) -> bool {
    |msg: Message|
        msg.dst.is_KubernetesAPI()
        && msg.content.is_delete_request()
        && msg.content.get_delete_request().key == make_stateful_set_key(key)
}

pub open spec fn sts_delete_request_msg_since(key: ObjectRef, rest_id: RestId) -> FnSpec(Message) -> bool {
    |msg: Message|
        sts_delete_request_msg(key)(msg)
        && msg.content.get_rest_id() >= rest_id
}

pub open spec fn no_delete_sts_req_since_rest_id_is_in_flight(
    key: ObjectRef, rest_id: RestId
) -> StatePred<ZKCluster>
    recommends
        key.kind.is_CustomResourceKind(),
{
    |s: ZKCluster| {
        forall |msg: Message| !{
            &&& #[trigger] s.message_in_flight(msg)
            &&& sts_delete_request_msg_since(key, rest_id)(msg)
        }
    }
}

pub proof fn lemma_always_no_delete_sts_req_since_rest_id_is_in_flight(
    spec: TempPred<ZKCluster>, key: ObjectRef, rest_id: RestId
)
    requires
        spec.entails(lift_state(ZKCluster::rest_id_counter_is(rest_id))),
        spec.entails(lift_state(ZKCluster::every_in_flight_msg_has_lower_id_than_allocator())),
        spec.entails(always(lift_action(ZKCluster::next()))),
        key.kind.is_CustomResourceKind(),
    ensures
        spec.entails(
            always(lift_state(no_delete_sts_req_since_rest_id_is_in_flight(key, rest_id)))
        ),
{
    let init = |s: ZKCluster| {
        &&& ZKCluster::rest_id_counter_is(rest_id)(s)
        &&& ZKCluster::every_in_flight_msg_has_lower_id_than_allocator()(s)
    };
    let next = ZKCluster::next();
    let invariant = no_delete_sts_req_since_rest_id_is_in_flight(key, rest_id);

    entails_and_n!(
        spec,
        lift_state(ZKCluster::rest_id_counter_is(rest_id)),
        lift_state(ZKCluster::every_in_flight_msg_has_lower_id_than_allocator())
    );
    temp_pred_equality(
        lift_state(init),
        lift_state(ZKCluster::rest_id_counter_is(rest_id))
        .and(lift_state(ZKCluster::every_in_flight_msg_has_lower_id_than_allocator()))
    );

    assert forall |s, s_prime: ZKCluster| invariant(s) && #[trigger] next(s, s_prime)
    implies invariant(s_prime) by {
        assert forall |msg: Message|
        !(#[trigger] s_prime.message_in_flight(msg) && sts_delete_request_msg_since(key, rest_id)(msg)) by {
            if s.message_in_flight(msg) {} else {}
        }
    }

    init_invariant(spec, init, next, invariant);
}

}
