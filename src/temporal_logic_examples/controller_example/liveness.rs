// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::controller_example::safety::*;
use crate::controller_example::state_machine::*;
use crate::pred::*;
use crate::temporal_logic::*;
use builtin::*;
use builtin_macros::*;

verus! {

spec fn sent1_state_pred() -> StatePred<CState> {
    StatePred::new(|state: CState| state.sent_1_create)
}

spec fn sent2_state_pred() -> StatePred<CState> {
    StatePred::new(|state: CState| state.sent_2_create)
}

spec fn obj1_state_pred() -> StatePred<CState> {
    StatePred::new(|state: CState| state.obj_1_exists)
}

spec fn obj2_state_pred() -> StatePred<CState> {
    StatePred::new(|state: CState| state.obj_2_exists)
}

proof fn reconcile_enabled()
    ensures forall |s: CState| send1_pre_state_pred().satisfied_by(s) || send2_pre_state_pred().satisfied_by(s) <==> #[trigger] enabled(reconcile_action_pred()).satisfied_by(s)
{
    /*
     * This is just a witness to show that reconcile is enabled
     * by send1_pre_state_pred() or send2_pre_state_pred()
     */

    assert forall |s: CState| send1_pre_state_pred().satisfied_by(s) implies #[trigger] enabled(reconcile_action_pred()).satisfied_by(s) by {
        if send1_pre_state_pred().satisfied_by(s) {
            let witness_action = Action {
                state: s,
                state_prime: CState {
                    sent_1_create: true,
                    messages: s.messages.insert(Message::CreateReq{id: 1}),
                    ..s
                }
            };
            assert(reconcile_action_pred().satisfied_by(witness_action));
        }
    };
    assert forall |s: CState| send2_pre_state_pred().satisfied_by(s) implies #[trigger] enabled(reconcile_action_pred()).satisfied_by(s) by {
        if send2_pre_state_pred().satisfied_by(s) {
            let witness_action = Action {
                state: s,
                state_prime: CState {
                    sent_2_create: true,
                    messages: s.messages.insert(Message::CreateReq{id: 2}),
                    ..s
                }
            };
            assert(reconcile_action_pred().satisfied_by(witness_action));
        }
    };
}

proof fn create1_enabled()
    ensures forall |s: CState| create1_pre_state_pred().satisfied_by(s) <==> #[trigger] enabled(create1_action_pred()).satisfied_by(s)
{
    /*
     * This is just a witness to show that create1 is enabled
     * by create1_pre_state_pred()
     */

    assert forall |s: CState| create1_pre_state_pred().satisfied_by(s) implies #[trigger] enabled(create1_action_pred()).satisfied_by(s) by {
        let witness_action = Action {
            state: s,
            state_prime: CState {
                obj_1_exists: true,
                ..s
            }
        };
        assert(create1_action_pred().satisfied_by(witness_action));
    };
}

proof fn create2_enabled()
    ensures forall |s: CState| create2_pre_state_pred().satisfied_by(s) <==> #[trigger] enabled(create2_action_pred()).satisfied_by(s)
{
    /*
     * This is just a witness to show that create2 is enabled
     * by create2_pre_state_pred()
     */

    assert forall |s: CState| create2_pre_state_pred().satisfied_by(s) implies #[trigger] enabled(create2_action_pred()).satisfied_by(s) by {
        let witness_action = Action {
            state: s,
            state_prime: CState {
                obj_2_exists: true,
                ..s
            }
        };
        assert(create2_action_pred().satisfied_by(witness_action));
    };
}

proof fn prove_init_leads_to_obj1()
    ensures
        valid(implies(
            sm_spec(),
            leads_to(init_state_pred().lift(), obj1_state_pred().lift())
        ))
{
    /*
     * This proof is straightforward:
     * We get each individual leads_to from wf1 by providing the witness
     * and connect the leads_to together using leads_to_trans rule.
     */

    apply_implies_auto::<CState>();

    leads_to_weaken_auto::<CState>();

    reconcile_enabled();
    wf1::<CState>(next_action_pred(), reconcile_action_pred(), send1_pre_state_pred(), create1_pre_state_pred());

    create1_enabled();
    wf1::<CState>(next_action_pred(), create1_action_pred(), create1_pre_state_pred(), obj1_state_pred());

    leads_to_trans::<CState>(send1_pre_state_pred(), create1_pre_state_pred(), obj1_state_pred());
}

/*
 * To connect with the above leads_to and further prove
 * `valid(implies(sm_spec(), eventually(obj2_state_pred().lift()))`,
 * now we need to prove
 * `valid(implies(sm_spec(), leads_to(obj1_state_pred().lift(), obj2_state_pred().lift())))`.
 */

proof fn prove_obj1_leads_to_obj2()
    ensures
        valid(implies(
            sm_spec(),
            leads_to(obj1_state_pred().lift(), obj2_state_pred().lift())
        ))
{
    /*
     * This proof is interesting and quite complex.
     * Fasten your seat belt.
     */

    /*
     * apply_implies_auto is used to automatically apply the following rule:
     * valid(implies(p, q)) && p.satisfied_by(ex) ==> q.satisfied_by(ex)
     * without requiring the developer to write `assert forall |ex| ... implies ... by {...}` in the proof.
     */
    apply_implies_auto::<CState>();

    /*
     * leads_to_weaken_auto allows us to prove the desired leads_to
     * by proving a equivalently "strong" leads_to or a "stronger" leads_to
     * that is easier to be proved.
     * It seems that we are abusing this rule in this proof.
     * Hope there is a more efficient way to do this.
     */
    leads_to_weaken_auto::<CState>();

    /*
     * premise1 and premise2 are just two temporal predicates we will frequently use later.
     */
    let premise1 = and(
        obj1_state_pred().lift(),
        and(not(obj2_state_pred().lift()), not(sent2_state_pred().lift()))
    );
    let premise2 = and(
        obj1_state_pred().lift(),
        and(not(obj2_state_pred().lift()), sent2_state_pred().lift())
    );

    /*
     * Let's start from simple by connecting the leads_to from wf1 and see what we get.
     */
    reconcile_enabled();
    wf1::<CState>(next_action_pred(), reconcile_action_pred(), send2_pre_state_pred(), create2_pre_state_pred());

    create2_enabled();
    wf1::<CState>(next_action_pred(), create2_action_pred(), create2_pre_state_pred(), obj2_state_pred());

    leads_to_trans::<CState>(send2_pre_state_pred(), create2_pre_state_pred(), obj2_state_pred());

    // assert(valid(implies(
    //     sm_spec(),
    //     leads_to(send2_pre_state_pred().lift(), obj2_state_pred().lift())
    // )));

    // assert(valid(implies(
    //         sm_spec(),
    //         leads_to(premise1, obj2_state_pred().lift())
    // )));

    /*
     * By connecting the two leads_to, we will have:
     * `valid(implies(sm_spec(), leads_to(send2_pre_state_pred().lift(), obj2_state_pred().lift())))`
     *
     * Now we have a problem: we cannot connect this leads_to with
     * the previous leads_to from prove_init_leads_to_obj1()
     * because that one ends at:
     * `s.obj_1_exists`
     * but the one we just proved starts from:
     * `s.obj_1_exists && !s.obj_2_exists && !s.sent_2_create`.
     *
     * So we need to further prove the cases where:
     * `s.obj_2_exists || s.sent_2_create`.
     *
     * Note that the when `s.obj_2_exists == true` the proof is trivial,
     * so we can start from proving the case where:
     * `s.obj_1_exists && !s.obj_2_exists && s.sent_2_create`.
     */


    /*
     * Now, let's try to prove:
     * `valid(implies(sm_spec(), leads_to(premise2, obj2_state_pred().lift())))`.
     * The following proof is not that obvious. So please get prepared :)
     *
     * From above, we already have:
     * `leads_to(create2_pre_state_pred().lift(), obj2_state_pred().lift())`.
     *
     * We will need to waken this leads_to (automatically with leads_to_weaken_auto) to the following:
     * `leads_to(and(sent2_state_pred().lift(), msg_inv_state_pred().lift()), obj2_state_pred().lift())`.
     * Note that `msg_inv_state_pred()` is from the safety proof.
     *
     * This is not enough. We need to (automatically) waken the leads_to again to the following:
     * `leads_to(and(premise2, msg_inv_state_pred().lift()), obj2_state_pred().lift())`.
     */

    // assert(valid(implies(
    //     sm_spec(),
    //     leads_to(create2_pre_state_pred().lift(), obj2_state_pred().lift())
    // )));

    // assert(valid(implies(sm_spec(), leads_to(
    //     and(sent2_state_pred().lift(), msg_inv_state_pred().lift()),
    //     obj2_state_pred().lift()
    // ))));

    // assert(valid(implies(sm_spec(), leads_to(
    //     and(premise2, msg_inv_state_pred().lift()),
    //     obj2_state_pred().lift()
    // ))));

    /*
     * By calling prove_msg_inv, we have `always(msg_inv_state_pred().lift())`
     * and now we can use the leads_to_assume rule to eliminate
     * `msg_inv_state_pred().lift()` from the premise.
     */
    prove_msg_inv();
    leads_to_assume::<CState>(premise2, obj2_state_pred().lift(), msg_inv_state_pred().lift());

    // assert(valid(implies(sm_spec(), leads_to(
    //     premise2, obj2_state_pred().lift()
    // ))));

    /*
     * Now we use leads_to_or_split rule to combine
     * premise1 and premise2 together.
     */
    leads_to_or_split::<CState>(premise2, premise1, obj2_state_pred().lift());

    // assert(valid(implies(sm_spec(), leads_to(
    //     or(premise1, premise2),
    //     obj2_state_pred().lift()
    // ))));

    /*
     * With leads_to_weaken_auto,
     * Verus automatically knows the following fact
     * since the two leads_to are equally strong.
     */

    // assert(valid(implies(sm_spec(), leads_to(
    //     and(
    //         obj1_state_pred().lift(),
    //         not(obj2_state_pred().lift()),
    //     ),
    //     obj2_state_pred().lift()
    // ))));

    /*
     * We are very close to our goal!
     * The last thing to do is to eliminate `not(obj2_state_pred().lift())`
     * with leads_to_assume_not rule.
     */
    leads_to_assume_not::<CState>(obj1_state_pred().lift(), obj2_state_pred().lift());
}

proof fn prove_eventually_obj1()
    ensures
        valid(implies(sm_spec(), eventually(obj1_state_pred().lift())))
{
    /*
     * This proof is simple: just take the leads_to from prove_init_leads_to_obj1()
     * and use leads_to_apply rule to get eventually from leads_to.
     */

    apply_implies_auto::<CState>();

    prove_init_leads_to_obj1();

    leads_to_apply::<CState>(init_state_pred(), obj1_state_pred());
}

proof fn prove_eventually_obj2()
    ensures
        valid(implies(sm_spec(), eventually(obj2_state_pred().lift())))
{
    /*
     * This proof is also simple: just take the two leads_to
     * from prove_init_leads_to_obj1() and prove_obj1_leads_to_obj2(),
     * connect them together with leads_to_trans rule
     * and use leads_to_apply rule to get eventually from leads_to.
     */

    apply_implies_auto::<CState>();

    prove_init_leads_to_obj1();

    prove_obj1_leads_to_obj2();

    leads_to_trans::<CState>(init_state_pred(), obj1_state_pred(), obj2_state_pred());

    leads_to_apply::<CState>(init_state_pred(), obj2_state_pred());
}

proof fn prove_liveness()
    ensures
        valid(implies(
            sm_spec(),
            eventually(and(obj1_state_pred().lift(), obj2_state_pred().lift()))
        )),
{
    /*
     * This proof needs the safety property we proved in safety.rs.
     * We use always_and_eventually rule to combine
     * the eventually from prove_eventually_obj2()
     * and the always from prove_safety()
     * to one eventually.
     *
     * Note that safety_state_pred() and obj2_state_pred() together
     * imply obj1_state_pred().
     */

    apply_implies_auto::<CState>();

    prove_eventually_obj2();
    // assert(valid(implies(sm_spec(), eventually(obj2_state_pred().lift()))));

    prove_safety();
    // assert(valid(implies(sm_spec(), always(safety_state_pred().lift()))));

    always_and_eventually::<CState>(safety_state_pred().lift(), obj2_state_pred().lift());
    // assert(valid(implies(
    //     sm_spec(),
    //     eventually(and(safety_state_pred().lift(), obj2_state_pred().lift()))
    // )));

    eventually_weaken::<CState>(and(safety_state_pred().lift(), obj2_state_pred().lift()), and(obj1_state_pred().lift(), obj2_state_pred().lift()));

}

}
