// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::concurrent_controller_example::state_machine::*;
use crate::pervasive::string::*;
use crate::temporal_logic::*;
use builtin::*;
use builtin_macros::*;

verus! {

pub open spec fn create_cr_msg() -> Message {
    Message::CreateCR
}

pub open spec fn create_sts_msg() -> Message {
    Message::CreateStatefulSet{replica: 1}
}

pub open spec fn create_vol_msg() -> Message {
    Message::CreateVolume{id: 1}
}

// TODO: ideally, we should not need to specify the weak_fairness for each msg separately
// This should be part of sm_spec(), but the current temporal logic API does not support that.
spec fn augmented_sm_spec() -> TempPred<CState> {
    sm_spec()
    .and(weak_fairness(k8s_handle_create_concretized(create_cr_msg())))
    .and(weak_fairness(k8s_handle_create_concretized(create_sts_msg())))
}

proof fn lemma_init_leads_to_pod1_exists()
    ensures
        valid(augmented_sm_spec()
            .implies(init().lift()
                .leads_to(pod1_exists().lift()))),
{
    leads_to_eq_auto::<CState>(augmented_sm_spec());

    send_create_cr_enabled();
    wf1::<CState>(augmented_sm_spec(),
        next(),
        send_create_cr(),
        init(),
        create_cr_sent()
    );

    k8s_handle_any_create_msg_pre_implies_enabled(create_cr_msg());
    wf1::<CState>(
        augmented_sm_spec(),
        next(),
        k8s_handle_create_concretized(create_cr_msg()),
        k8s_handle_create_pre_concretized(create_cr_msg()),
        k8s_handle_create_post_concretized(create_cr_msg())
    );

    leads_to_trans::<CState>(augmented_sm_spec(),
        init().lift(),
        create_cr_sent().lift(),
        cr_exists().lift()
    );

    send_create_sts_enabled();
    wf1::<CState>(augmented_sm_spec(),
        next(),
        send_create_sts(),
        send_create_sts_precondition(),
        create_sts_sent()
    );
    leads_to_assume_not::<CState>(augmented_sm_spec(),
        cr_exists().lift(),
        create_sts_sent().lift()
    );

    k8s_handle_any_create_msg_pre_implies_enabled(create_sts_msg());
    wf1::<CState>(augmented_sm_spec(),
        next(),
        k8s_handle_create_concretized(create_sts_msg()),
        k8s_handle_create_pre_concretized(create_sts_msg()),
        k8s_handle_create_post_concretized(create_sts_msg()),
    );

    leads_to_trans::<CState>(augmented_sm_spec(),
        cr_exists().lift(),
        create_sts_sent().lift(),
        sts_exists().lift()
    );

    k8s_create_pod_enabled();
    wf1::<CState>(augmented_sm_spec(),
        next(),
        k8s_create_pod(),
        sts_exists(),
        pod1_exists()
    );
    leads_to_trans::<CState>(augmented_sm_spec(),
        cr_exists().lift(),
        sts_exists().lift(),
        pod1_exists().lift()
    );

    leads_to_trans::<CState>(augmented_sm_spec(),
        init().lift(),
        cr_exists().lift(),
        pod1_exists().lift()
    );
}

}
