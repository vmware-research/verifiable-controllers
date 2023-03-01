// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_cluster::spec::common::*;
use crate::pervasive::option::*;
use builtin::*;
use builtin_macros::*;

verus! {

/// Reconciler is the key data structure we use to pack up all the custom controller-specific logic
/// and install it to the Kubernetes cluster state machine
pub struct Reconciler<#[verifier(maybe_negative)] T> {
    // reconcile_init_state returns the initial local state that the reconciler starts
    // its reconcile function with.
    // Currently the local state is hardcoded to a ReconcileState.
    // We would like to make ReconcileState more general and reconcile_init_state
    // can also be more flexible.
    pub reconcile_init_state: ReconcileInitState<T>,

    // reconcile_trigger decides whether the reconcile function should be triggered by an incoming event
    // The trigger condition can be as simple as "trigger only when the CR gets changed".
    // It can also be more complex and checks ownership and other relationships
    // so the reconcile function is also triggered when sub-resources gets changed.
    pub reconcile_trigger: ReconcileTrigger,

    // reconcile_core describes the logic of reconcile function and is the key logic we want to verify.
    // Each reconcile_core should take the local state and a response of the previous request (if any) as input
    // and outputs the next local state and the request to send to Kubernetes API (if any).
    pub reconcile_core: ReconcileCore<T>,

    // reconcile_done is used to tell the controller_runtime whether the reconcile function finishes.
    // If it is true, controller_runtime will cleans up its local state and probably requeue the reconcile.
    pub reconcile_done: ReconcileDone<T>,
}

pub type ReconcileInitState<T> = FnSpec() -> T;

pub type ReconcileTrigger = FnSpec(Message) -> Option<ResourceKey>;

pub type ReconcileCore<T> = FnSpec(ResourceKey, Option<APIResponse>, T) -> (T, Option<APIRequest>);

pub type ReconcileDone<T> = FnSpec(T) -> bool;

}