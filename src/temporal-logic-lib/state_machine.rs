// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::action::*;
use crate::pervasive::{option::*, set::*};
use builtin::*;
use builtin_macros::*;

verus! {

/// `HostStateMachine` helps to write host state machines in a disciplined way
/// by explicitly writing `init`, `actions`, and `result`.
///
/// It takes four generic types:
/// * `State`: The (internal) state of the host.
/// * `Input`: The input from the external world of the state machine. For example a message.
/// * `ActionInput`: The input to feed to the action. It might be a compound of `Input` and other types.
/// * `Output`: The output to send to the external world of the state machine. For example a set of messages.
pub struct HostStateMachine <
    #[verifier(maybe_negative)] State,
    #[verifier(maybe_negative)] Input,
    #[verifier(maybe_negative)] ActionInput,
    #[verifier(maybe_negative)] Output,
    #[verifier(maybe_negative)] Step,
> {
    /// Check if it is the initial internal state.
    pub init: FnSpec(State) -> bool,

    /// The set of actions the state machine can take.
    pub actions: Set<HostAction<State, ActionInput, Output>>,

    pub step_to_action: FnSpec(Step) -> HostAction<State, ActionInput, Output>,

    pub step_to_action_input: FnSpec(Step, Input) -> ActionInput,
}

impl<State, Input, ActionInput, Output, Step> HostStateMachine<State, Input, ActionInput, Output, Step> {
    pub open spec fn next_result(self, input: Input, s: State) -> HostActionResult<State, Output> {
        if exists |step| (#[trigger] (self.step_to_action)(step).precondition)((self.step_to_action_input)(step, input), s) {
            let witness_step = choose |step| (#[trigger] (self.step_to_action)(step).precondition)((self.step_to_action_input)(step, input), s);
            let action = (self.step_to_action)(witness_step);
            let action_input = (self.step_to_action_input)(witness_step, input);
            HostActionResult::Enabled((action.transition)(action_input, s).0, (action.transition)(action_input, s).1)
        } else {
            HostActionResult::Disabled
        }
    }
}

pub struct NetworkStateMachine <#[verifier(maybe_negative)] State, #[verifier(maybe_negative)] Message> {
    /// Check if it is the initial internal state.
    pub init: FnSpec(State) -> bool,

    /// The deliver action that (1) sends zero or one message to a host and (2) takes any number of messages from a host.
    pub deliver: NetworkAction<State, Message>,
}

impl<State, Message> NetworkStateMachine<State, Message> {
    pub open spec fn next_result(self, recv: Option<Message>, s: State, send: Set<Message>) -> NetworkActionResult<State> {
        if (self.deliver.precondition)(recv, s) {
            NetworkActionResult::Enabled((self.deliver.transition)(recv, s, send))
        } else {
            NetworkActionResult::Disabled
        }
    }
}

}
