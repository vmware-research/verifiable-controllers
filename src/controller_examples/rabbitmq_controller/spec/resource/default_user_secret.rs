// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use super::common::*;
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::{
    container::*, label_selector::*, pod_template_spec::*, prelude::*, resource_requirements::*,
    volume::*,
};
use crate::kubernetes_cluster::spec::message::*;
use crate::pervasive_ext::string_view::*;
use crate::rabbitmq_controller::common::*;
use crate::rabbitmq_controller::spec::types::*;
use crate::reconciler::spec::{io::*, reconciler::*};
use crate::state_machine::{action::*, state_machine::*};
use crate::temporal_logic::defs::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {

pub struct DefaultUserSecretBuilder {}

impl ResourceBuilder<SecretView> for DefaultUserSecretBuilder {
    open spec fn make(rabbitmq: RabbitmqClusterView, state: RabbitmqReconcileState) -> Result<SecretView, RabbitmqError> {
        Ok(make_default_user_secret(rabbitmq))
    }

    open spec fn update(rabbitmq: RabbitmqClusterView, state: RabbitmqReconcileState, found_resource: SecretView) -> Result<SecretView, RabbitmqError> {
        Ok(update_default_user_secret(rabbitmq, found_resource))
    }
}

pub open spec fn make_default_user_secret_name(rabbitmq: RabbitmqClusterView) -> StringView
    recommends
        rabbitmq.metadata.name.is_Some(),
{
    rabbitmq.metadata.name.get_Some_0() + new_strlit("-default-user")@
}

pub open spec fn make_default_user_secret_key(rabbitmq: RabbitmqClusterView) -> ObjectRef
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    ObjectRef {
        kind: SecretView::kind(),
        name: make_default_user_secret_name(rabbitmq),
        namespace: rabbitmq.metadata.namespace.get_Some_0(),
    }
}

pub open spec fn update_default_user_secret(rabbitmq: RabbitmqClusterView, found_secret: SecretView) -> SecretView
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    let made_secret = make_default_user_secret(rabbitmq);
    SecretView {
        metadata: ObjectMetaView {
            owner_references: Some(make_owner_references(rabbitmq)),
            finalizers: None,
            labels: made_secret.metadata.labels,
            annotations: made_secret.metadata.annotations,
            ..found_secret.metadata
        },
        ..found_secret
    }
}

pub open spec fn make_default_user_secret(rabbitmq: RabbitmqClusterView) -> SecretView
    recommends
        rabbitmq.metadata.name.is_Some(),
        rabbitmq.metadata.namespace.is_Some(),
{
    let data = Map::empty()
        .insert(new_strlit("username")@, new_strlit("user")@)
        .insert(new_strlit("password")@, new_strlit("changeme")@)
        .insert(new_strlit("type")@, new_strlit("rabbitmq")@)
        .insert(new_strlit("host")@,
            rabbitmq.metadata.name.get_Some_0() + new_strlit(".")@ + rabbitmq.metadata.namespace.get_Some_0() + new_strlit(".svc")@,
        )
        .insert(new_strlit("provider")@, new_strlit("rabbitmq")@)
        .insert(new_strlit("default_user.conf")@, new_strlit("default_user = user\ndefault_pass = changeme")@)
        .insert(new_strlit("port")@, new_strlit("5672")@);
    make_secret(rabbitmq, make_default_user_secret_name(rabbitmq), data)
}

}
