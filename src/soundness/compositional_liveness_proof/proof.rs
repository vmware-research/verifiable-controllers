// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::soundness::compositional_liveness_proof::state_machine::*;
use crate::temporal_logic::defs::*;
use vstd::prelude::*;

verus! {

closed spec fn a_property<S>() -> TempPred<S>;

closed spec fn b_property<S>() -> TempPred<S>;

proof fn b_property_holds_globally<S, I>(spec: TempPred<S>)
    requires
        spec.entails(lift_state(init::<S>())),
        spec.entails(always(lift_action(next::<S, I>()))),
        spec.entails(fairness::<S>()),
    ensures
        spec.entails(b_property::<S>()),
{
    assert forall |ex| #[trigger] spec.satisfied_by(ex)
    implies always(lift_action(next_with_a_only::<S, I>())).satisfied_by(ex) by {
        assert(spec.implies(always(lift_action(next::<S, I>()))).satisfied_by(ex));
        assert forall |i| #[trigger] lift_action(next_with_a_only::<S, I>()).satisfied_by(ex.suffix(i)) by {
            assert(lift_action(next::<S, I>()).satisfied_by(ex.suffix(i)));
            next_does_nothing_beyond_next_with_a_only::<S, I>(ex.suffix(i).head(), ex.suffix(i).head_next());
        }
    }

    assert forall |ex| #[trigger] spec.satisfied_by(ex)
    implies always(lift_action(next_with_b_only::<S, I>())).satisfied_by(ex) by {
        assert(spec.implies(always(lift_action(next::<S, I>()))).satisfied_by(ex));
        assert forall |i| #[trigger] lift_action(next_with_b_only::<S, I>()).satisfied_by(ex.suffix(i)) by {
            assert(lift_action(next::<S, I>()).satisfied_by(ex.suffix(i)));
            next_does_nothing_beyond_next_with_b_only::<S, I>(ex.suffix(i).head(), ex.suffix(i).head_next());
        }
    }

    a_inv_holds_locally::<S, I>(spec);
    b_property_holds_locally::<S, I>(spec);
}

proof fn a_property_holds_globally<S, I>(spec: TempPred<S>)
    requires
        spec.entails(lift_state(init::<S>())),
        spec.entails(always(lift_action(next::<S, I>()))),
        spec.entails(fairness::<S>()),
        spec.entails(b_property::<S>()),
    ensures
        spec.entails(a_property::<S>()),
{
    assert forall |ex| #[trigger] spec.satisfied_by(ex)
    implies always(lift_action(next_with_a_only::<S, I>())).satisfied_by(ex) by {
        assert(spec.implies(always(lift_action(next::<S, I>()))).satisfied_by(ex));
        assert forall |i| #[trigger] lift_action(next_with_a_only::<S, I>()).satisfied_by(ex.suffix(i)) by {
            assert(lift_action(next::<S, I>()).satisfied_by(ex.suffix(i)));
            next_does_nothing_beyond_next_with_a_only::<S, I>(ex.suffix(i).head(), ex.suffix(i).head_next());
        }
    }

    assert forall |ex| #[trigger] spec.satisfied_by(ex)
    implies always(lift_action(next_with_b_only::<S, I>())).satisfied_by(ex) by {
        assert(spec.implies(always(lift_action(next::<S, I>()))).satisfied_by(ex));
        assert forall |i| #[trigger] lift_action(next_with_b_only::<S, I>()).satisfied_by(ex.suffix(i)) by {
            assert(lift_action(next::<S, I>()).satisfied_by(ex.suffix(i)));
            next_does_nothing_beyond_next_with_b_only::<S, I>(ex.suffix(i).head(), ex.suffix(i).head_next());
        }
    }

    b_property_holds_globally::<S, I>(spec);
    b_inv_holds_locally::<S, I>(spec);
    a_property_holds_locally::<S, I>(spec);
}

proof fn next_does_nothing_beyond_next_with_a_only<S, I>(s: S, s_prime: S)
    requires
        next::<S, I>()(s, s_prime),
    ensures
       next_with_a_only::<S, I>()(s, s_prime),
{
    let step = choose |step: Step<I>| next_step(s, s_prime, step);
    assert(next_step(s, s_prime, step));
    match step {
        Step::ControllerBStep(input) => {
            let env_input = b_does_nothing_beyond_what_env_does::<S, I>(input);
            assert(next_step_with_a_only(s, s_prime, Step::EnvStep(env_input)));
        }
        _ => {
            assert(next_step_with_a_only(s, s_prime, step));
        }
    }
}

proof fn next_does_nothing_beyond_next_with_b_only<S, I>(s: S, s_prime: S)
    requires
        next::<S, I>()(s, s_prime),
    ensures
       next_with_b_only::<S, I>()(s, s_prime),
{
    let step = choose |step: Step<I>| next_step(s, s_prime, step);
    assert(next_step(s, s_prime, step));
    match step {
        Step::ControllerAStep(input) => {
            let env_input = a_does_nothing_beyond_what_env_does::<S, I>(input);
            assert(next_step_with_b_only(s, s_prime, Step::EnvStep(env_input)));
        }
        _ => {
            assert(next_step_with_b_only(s, s_prime, step));
        }
    }
}

closed spec fn a_inv<S>() -> StatePred<S>;

closed spec fn b_inv<S>() -> StatePred<S>;

#[verifier(external_body)]
proof fn b_inv_holds_locally<S, I>(spec: TempPred<S>)
    requires
        spec.entails(lift_state(init::<S>())),
        spec.entails(always(lift_action(next_with_b_only::<S, I>()))),
    ensures
        spec.entails(always(lift_state(b_inv::<S>()))),
{}

#[verifier(external_body)]
proof fn a_does_nothing_beyond_what_env_does<S, I>(input: I) -> (env_input: I)
    ensures forall |s, s_prime: S| #[trigger] controller_a_next(input)(s, s_prime)
            ==> environment_next(env_input)(s, s_prime)
{
    arbitrary()
}

#[verifier(external_body)]
proof fn b_property_holds_locally<S, I>(spec: TempPred<S>)
    requires
        spec.entails(lift_state(init::<S>())),
        spec.entails(always(lift_action(next_with_b_only::<S, I>()))),
        spec.entails(fairness::<S>()),
        spec.entails(always(lift_state(a_inv::<S>()))),
    ensures
        spec.entails(b_property::<S>()),
{}

#[verifier(external_body)]
proof fn a_inv_holds_locally<S, I>(spec: TempPred<S>)
    requires
        spec.entails(lift_state(init::<S>())),
        spec.entails(always(lift_action(next_with_a_only::<S, I>()))),
    ensures
        spec.entails(always(lift_state(a_inv::<S>()))),
{}

#[verifier(external_body)]
proof fn b_does_nothing_beyond_what_env_does<S, I>(input: I) -> (env_input: I)
    ensures forall |s, s_prime: S| #[trigger] controller_b_next(input)(s, s_prime)
            ==> environment_next(env_input)(s, s_prime)
{
    arbitrary()
}

#[verifier(external_body)]
proof fn a_property_holds_locally<S, I>(spec: TempPred<S>)
    requires
        spec.entails(lift_state(init::<S>())),
        spec.entails(always(lift_action(next_with_a_only::<S, I>()))),
        spec.entails(fairness::<S>()),
        spec.entails(always(lift_state(b_inv::<S>()))),
        spec.entails(b_property::<S>()),
    ensures
        spec.entails(a_property::<S>()),
{}

}
