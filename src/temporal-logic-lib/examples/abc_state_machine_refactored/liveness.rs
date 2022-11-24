// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::examples::abc_state_machine::state_machine::*;
use crate::temporal_logic::*;
use builtin::*;
use builtin_macros::*;

verus! {

proof fn eventually_c()
    ensures
        sm_spec().entails(
            eventually(lift_state(c()))
        ),
{
    // D:
    a_b_enabled();
    b_c_enabled();

    // F:
    assert(forall |s, s_prime| a()(s) && action_pred_call(next(), s, s_prime) ==> a()(s_prime) || b()(s_prime));
    assert(forall |s, s_prime| a()(s) && action_pred_call(next(), s, s_prime) && a_b()(s, s_prime) ==> b()(s_prime));
    assert(forall |s, s_prime| b()(s) && action_pred_call(next(), s, s_prime) ==> b()(s_prime) || c()(s_prime));
    assert(forall |s, s_prime| b()(s) && action_pred_call(next(), s, s_prime) && b_c()(s, s_prime) ==> c()(s_prime));

    // temporal:
    wf1::<SimpleState>(sm_spec(), next(), a_b(), a(), b());
    wf1::<SimpleState>(sm_spec(), next(), b_c(), b(), c());
    leads_to_trans::<SimpleState>(sm_spec(), a(), b(), c());
    leads_to_apply::<SimpleState>(sm_spec(), a(), c());
}

}
