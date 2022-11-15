// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::pervasive::{option::*, set::*};
use builtin::*;
use builtin_macros::*;

verus! {

/// `HostAction` helps to write host actions in a disciplined way
/// by explicitly writing `precondition`, `transition` and `output`.
///
/// It takes three generic types:
/// * `State`: The (internal) state of the host.
/// * `Input`: The input from the external world of the state machine. For example a message.
/// * `Output`: The output to send to the external world of the state machine. For example a set of messages.
///
/// It has three members:
/// * `precondition`: The condition that enables the host action.
/// * `transition`: The transition made to the internal state by the action.
/// * `output`: The output generated by the action.
pub struct HostAction<#[verifier(maybe_negative)] State, #[verifier(maybe_negative)] Input, #[verifier(maybe_negative)] Output> {
    pub precondition: FnSpec(Input, State) -> bool,
    pub transition: FnSpec(Input, State) -> State,
    pub output: FnSpec(Input, State) -> Output,
}

impl<State, Input, Output> HostAction<State, Input, Output> {

    /// `satisfied_by` is like an action predicate:
    /// it checks whether the action's precondition is satisfied by `input` and `s`
    /// and whether the `s_prime` is the same as the new state after transition.
    /// It is supposed to be called inside each host state machine's `next`.
    ///
    /// Note that it does not check the `output` sent to the external world.
    pub open spec fn satisfied_by(self, input: Input, s: State, s_prime: State) -> bool {
        &&& (self.precondition)(input, s)
        &&& s_prime === (self.transition)(input, s)
    }
}

/// `NetworkAction` helps to write network actions in a disciplined way
/// by explicitly writing `precondition` and `transition`.
///
/// It takes two generic types:
/// * `State`: The (internal) state of the network. For example, messages on the fly.
/// * `Message`: The message that the network receives and sends.
///
/// It has two members:
/// * `precondition`: The condition that enables the network action. For example, whether the delivered message was sent before.
/// * `transition`: The transition made to the internal state by the action. For example, record all the messages the host sends in this step.
pub struct NetworkAction<#[verifier(maybe_negative)] State, #[verifier(maybe_negative)] Message> {
    pub precondition: FnSpec(Option<Message>, State) -> bool,
    pub transition: FnSpec(Option<Message>, State, Set<Message>) -> State,
}

impl<State, Message> NetworkAction<State, Message> {
    pub open spec fn satisfied_by(self, recv: Option<Message>, s: State, s_prime: State, send: Set<Message>) -> bool {
        &&& (self.precondition)(recv, s)
        &&& s_prime === (self.transition)(recv, s, send)
    }
}

}
