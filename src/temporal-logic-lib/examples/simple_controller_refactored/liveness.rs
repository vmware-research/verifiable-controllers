// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::examples::simple_controller::safety::*;
use crate::examples::simple_controller::state_machine::*;
use crate::temporal_logic::*;
use builtin::*;
use builtin_macros::*;

verus! {

spec fn sent1() -> StatePred<CState> {
    |s: CState| s.sent_1_create
}

spec fn sent2() -> StatePred<CState> {
    |s: CState| s.sent_2_create
}

spec fn obj1_exists() -> StatePred<CState> {
    |s: CState| s.obj_1_exists
}

spec fn obj2_exists() -> StatePred<CState> {
    |s: CState| s.obj_2_exists
}

spec fn obj1_exists_and_not_sent2() -> StatePred<CState> {
    |s: CState| s.obj_1_exists && !s.sent_2_create
}

proof fn lemma_init_leads_to_obj1_exists()
    ensures
        sm_spec().entails(
            lift_state(init())
                .leads_to(lift_state(obj1_exists()))
        ),
{
    // D:
    send1_enabled();
    create1_enabled();

    // F:
    assert(forall |s, s_prime: T| send1_pre()(s) && action_pred_call(next, s, s_prime) ==> send1_pre()(s_prime) || create1_pre()(s_prime));
    assert(forall |s, s_prime: T| send1_pre()(s) && action_pred_call(next, s, s_prime) && reconcile()(s, s_prime) ==> create1_pre()(s_prime));
    assert(forall |s, s_prime: T| create1_pre()(s) && action_pred_call(next, s, s_prime) ==> create1_pre()(s_prime) || obj1_exists()(s_prime));
    assert(forall |s, s_prime: T| create1_pre()(s) && action_pred_call(next, s, s_prime) && create1()(s, s_prime) ==> obj1_exists()(s_prime));
    
    // temporal:
    leads_to_weaken_lite_auto::<CState>(sm_spec());
    wf1::<CState>(sm_spec(), next(), reconcile(), send1_pre(), create1_pre());    
    wf1::<CState>(sm_spec(), next(), create1(), create1_pre(), obj1_exists());
    leads_to_trans::<CState>(sm_spec(), send1_pre(), create1_pre(), obj1_exists());
}

proof fn lemma_obj1_exists_and_not_sent2_leads_to_obj2_exists()
    ensures
        sm_spec().entails(
            lift_state(obj1_exists())
                .and(not(lift_state(sent2())))
                    .leads_to(lift_state(obj2_exists()))
        ),
{
    // D:
    send2_enabled();
    create2_enabled();

    // F:
    assert(forall |s, s_prime: T| send2_pre()(s) && action_pred_call(next, s, s_prime) ==> send2_pre()(s_prime) || create2_pre()(s_prime));
    assert(forall |s, s_prime: T| send2_pre()(s) && action_pred_call(next, s, s_prime) && reconcile()(s, s_prime) ==> create2_pre()(s_prime));
    assert(forall |s, s_prime: T| create2_pre()(s) && action_pred_call(next, s, s_prime) ==> create2_pre()(s_prime) || obj2_exists()(s_prime));
    assert(forall |s, s_prime: T| create2_pre()(s) && action_pred_call(next, s, s_prime) && create2()(s, s_prime) ==> obj2_exists()(s_prime));
    
    // temporal:
    leads_to_weaken_lite_auto::<CState>(sm_spec());
    wf1::<CState>(sm_spec(), next(), reconcile(), send2_pre(), create2_pre());
    wf1::<CState>(sm_spec(), next(), create2(), create2_pre(), obj2_exists());
    leads_to_trans::<CState>(sm_spec(), send2_pre(), create2_pre(), obj2_exists());
    leads_to_assume_not::<CState>(sm_spec(), obj1_exists_and_not_sent2(), obj2_exists());
}

/*
 * This invariant itself is straightforward.
 * We will use it in the next proof.
 */
proof fn lemma_msg_inv()
    ensures
        sm_spec().entails(
            always(lift_state(msg_inv()))
        ),
{
    // F:
    assert(forall |s: T| state_pred_call(init, s) ==> msg_inv(s));
    assert(forall |s, s_prime: T| msg_inv(s) && action_pred_call(next, s, s_prime) ==> msg_inv(s_prime));

    // temporal:
    init_invariant::<CState>(sm_spec(), init(), next(), msg_inv());
}

proof fn lemma_obj1_exists_and_sent2_leads_to_obj2_exists()
    ensures
        sm_spec().entails(
            lift_state(obj1_exists())
                .and(lift_state(sent2()))
                    .leads_to(lift_state(obj2_exists()))
        ),
{
    // D:
    create2_enabled();

    // F:
    // 2 lines from above
    assert(forall |s: T| state_pred_call(init, s) ==> inv(s));
    assert(forall |s, s_prime: T| msg_inv(s) && action_pred_call(next, s, s_prime) ==> msg_inv(s_prime));

    // temporal:
    leads_to_weaken_lite_auto::<CState>(sm_spec());
    wf1::<CState>(sm_spec(), next(), create2(), create2_pre(), obj2_exists());
    assert(sm_spec().entails(
        lift_state(sent2())
            .and(lift_state(msg_inv()))
                .leads_to(lift_state(obj2_exists()))
    ));

    /*
     * Thanks `msg_inv` for giving us `s.sent_2_create`.
     * Now let's get rid of `msg_inv` since it does not appear in our goal :)
     *
     * Our new friend `leads_to_assume` allows us to remove it since `lemma_msg_inv` shows `msg_inv` always holds.
     */
    lemma_msg_inv();
    leads_to_assume::<CState>(sm_spec(), sent2(), obj2_exists(), msg_inv());
}


/*
 * To connect with the above leads_to and further prove
 * `sm_spec().entails(eventually(lift_state(obj2_exists())))`,
 * now we need to prove
 * `sm_spec().entails(leads_to(lift_state(obj1_exists()), lift_state(obj2_exists())))`.
 */

proof fn lemma_obj1_exists_leads_to_obj2_exists()
    ensures
        sm_spec().entails(
            lift_state(obj1_exists())
                .leads_to(lift_state(obj2_exists()))
        ),
{
    // temporal:

    leads_to_weaken_lite_auto::<CState>(sm_spec());
    lemma_obj1_exists_and_not_sent2_leads_to_obj2_exists();
    lemma_obj1_exists_and_sent2_leads_to_obj2_exists();
    leads_to_combine::<CState>(sm_spec(), obj1_exists(), obj2_exists(), sent2());
}

proof fn lemma_eventually_obj1_exists()
    ensures
        sm_spec().entails(eventually(lift_state(obj1_exists()))),
{
    // temporal:
    lemma_init_leads_to_obj1_exists();
    leads_to_apply::<CState>(sm_spec(), init(), obj1_exists());
}

proof fn lemma_eventually_obj2_exits()
    ensures
        sm_spec().entails(eventually(lift_state(obj2_exists()))),
{
    // temporal:
    lemma_init_leads_to_obj1_exists();
    lemma_obj1_exists_leads_to_obj2_exists();
    leads_to_trans::<CState>(sm_spec(), init(), obj1_exists(), obj2_exists());
    leads_to_apply::<CState>(sm_spec(), init(), obj2_exists());
}

proof fn liveness()
    ensures
        sm_spec().entails(eventually(lift_state(obj1_exists()).and(lift_state(obj2_exists())))),
{

    // F:
    inductive(inductive_inv);

    // temporal:
    lemma_eventually_obj2_exits();
    safety();
    always_and_eventually::<CState>(sm_spec(), order_inv(), obj2_exists());
    eventually_weaken_auto::<CState>(sm_spec());
}

}
