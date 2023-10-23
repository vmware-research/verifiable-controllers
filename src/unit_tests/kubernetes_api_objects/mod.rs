// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
pub mod config_map;
pub mod configmap_projection;
pub mod configmap_volume_source;
pub mod container;
pub mod downwardapi_volume_file;
pub mod downwardapi_volume_source;
pub mod empty_dir_volume_source;
pub mod env_var;
pub mod env_var_source;
pub mod execaction;
pub mod hostpath_volume_source;
pub mod key_to_path;
pub mod label_selector;
pub mod lifecycle;
pub mod lifecycle_handler;
pub mod object_field_selector;
pub mod object_meta;
pub mod persistent_volume_claim;
pub mod persistent_volume_claim_spec;
pub mod pod;
pub mod pod_spec;
pub mod pod_template_spec;
pub mod policy_rule;
pub mod probe;
pub mod projected_volume_source;
pub mod resource_requirements;
pub mod role;
pub mod role_binding;
pub mod role_ref;
pub mod secret;
pub mod secret_projection;
pub mod secret_volume_source;
pub mod service;
pub mod service_account;
pub mod service_port;
pub mod service_spec;
pub mod stateful_set;
pub mod stateful_set_pvc_retention_policy;
pub mod stateful_set_spec;
pub mod subject;
pub mod tcp_socket_action;
pub mod volume;
pub mod volume_mount;
pub mod volume_projection;
