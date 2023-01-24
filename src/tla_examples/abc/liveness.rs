// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::temporal_logic::defs::*;
use crate::temporal_logic::rules::*;
use crate::tla_examples::abc::state_machine::*;
use builtin::*;
use builtin_macros::*;

verus! {

proof fn eventually_c()
    ensures
        sm_spec().entails(
            eventually(lift_state(c()))
        ),
{
    wf1_broadcast::<SimpleState>();

    // a_b_enabled() gives a witness to convince Verus that x === A enables a_b()
    a_b_enabled();

    // a_b_enabled() gives a witness to convince Verus that x === B enables b_c()
    b_c_enabled();

    // leads_to_trans connects the two leads_to together
    leads_to_trans::<SimpleState>(sm_spec(), a(), b(), c());

    // leads_to_apply gives us eventually from leads_to
    leads_to_apply::<SimpleState>(sm_spec(), a(), c());
}

}
