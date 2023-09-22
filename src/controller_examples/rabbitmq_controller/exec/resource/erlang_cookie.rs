// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use super::common::*;
use crate::external_api::exec::*;
use crate::kubernetes_api_objects::resource::ResourceWrapper;
use crate::kubernetes_api_objects::{
    container::*, label_selector::*, pod_template_spec::*, prelude::*, resource_requirements::*,
    volume::*,
};
use crate::pervasive_ext::string_map::StringMap;
use crate::pervasive_ext::string_view::*;
use crate::rabbitmq_controller::common::*;
use crate::rabbitmq_controller::exec::types::*;
use crate::rabbitmq_controller::spec::resource as spec_resource;
use crate::reconciler::exec::{io::*, reconciler::*};
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::string::*;

verus! {

pub fn update_erlang_secret(rabbitmq: &RabbitmqCluster, found_erlang_secret: Secret) -> (secret: Secret)
    requires
        rabbitmq@.metadata.name.is_Some(),
        rabbitmq@.metadata.namespace.is_Some(),
    ensures
        secret@ == spec_resource::update_erlang_secret(rabbitmq@, found_erlang_secret@),
{
    let mut erlang_secret = found_erlang_secret.clone();
    let made_secret = make_erlang_secret(rabbitmq);
    erlang_secret.set_metadata({
        let mut metadata = found_erlang_secret.metadata();
        let mut owner_references = Vec::new();
        owner_references.push(rabbitmq.controller_owner_ref());
        proof {
            assert_seqs_equal!(
                owner_references@.map_values(|owner_ref: OwnerReference| owner_ref@),
                spec_resource::update_erlang_secret(rabbitmq@, found_erlang_secret@).metadata.owner_references.get_Some_0()
            );
        }
        metadata.set_owner_references(make_owner_references(rabbitmq));
        metadata.unset_finalizers();
        metadata.set_labels(made_secret.metadata().labels().unwrap());
        metadata.set_annotations(made_secret.metadata().annotations().unwrap());
        metadata
    });
    erlang_secret
}

pub fn make_erlang_secret(rabbitmq: &RabbitmqCluster) -> (secret: Secret)
    requires
        rabbitmq@.metadata.name.is_Some(),
        rabbitmq@.metadata.namespace.is_Some(),
    ensures
        secret@ == spec_resource::make_erlang_secret(rabbitmq@)
{
    let mut data = StringMap::empty();
    let cookie = random_encoded_string(24);
    data.insert(new_strlit(".erlang.cookie").to_string(), cookie);
    make_secret(rabbitmq, rabbitmq.name().unwrap().concat(new_strlit("-erlang-cookie")), data)
}

#[verifier(external_body)]
pub fn random_encoded_string(data_len: usize) -> (cookie: String)
    ensures
        cookie@ == spec_resource::random_encoded_string(data_len),
{
    let random_bytes: std::vec::Vec<std::primitive::u8> = (0..data_len).map(|_| deps_hack::rand::random::<std::primitive::u8>()).collect();
    String::from_rust_string(deps_hack::base64::encode(random_bytes))
}

}
