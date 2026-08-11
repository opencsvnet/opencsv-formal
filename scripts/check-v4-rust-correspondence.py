#!/usr/bin/env python3
"""Fail closed if the pinned Rust v4 statement shape drifts from Lean.

This is deliberately a source-correspondence gate, not a Rust or AIR proof.
Lean proves the protocol semantics of the shape in OpenCsv/Forward.lean and
the recursive tree/version/distinctness rules in OpenCsv/Lineage.lean. This
script makes CI check that the exact pinned Rust source still exposes those
rules before the artifacts are described as corresponding.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def normalized(text: str) -> str:
    return re.sub(r"\s+", " ", text).strip()


def require(source: str, snippet: str, label: str) -> None:
    if normalized(snippet) not in normalized(source):
        raise SystemExit(f"v4 Rust correspondence failed: {label}")


def git_head(repo: Path) -> str:
    return subprocess.run(
        ["git", "-C", str(repo), "rev-parse", "HEAD"],
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--rust-dir", required=True, type=Path)
    args = parser.parse_args()

    pin = json.loads((ROOT / "rust-correspondence-v4.json").read_text())
    rust = args.rust_dir.resolve()
    actual = git_head(rust)
    if actual != pin["commit"]:
        raise SystemExit(
            "v4 Rust correspondence failed: checkout is "
            f"{actual}, expected pinned {pin['commit']}"
        )

    node = (rust / "crates/opencsv-pcd/src/node.rs").read_text()
    accept = (rust / "crates/opencsv-pcd/src/accept.rs").read_text()
    security = (rust / "crates/opencsv-pcd/src/security.rs").read_text()
    tests = (rust / "crates/opencsv-pcd/tests/node.rs").read_text()
    digest = (rust / "crates/opencsv-core/src/digest.rs").read_text()
    cli_ops = (rust / "crates/opencsv-cli/src/ops.rs").read_text()
    ffi_wallet = (rust / "ffi/src/wallet.rs").read_text()
    account = (rust / "ffi/src/account.rs").read_text()

    require(
        node,
        f"pub const LEGACY_COIN_PROOF_VERSION: u8 = {pin['legacy_proof_version']};",
        "legacy v3 boundary changed",
    )
    require(
        node,
        f"pub const COIN_PROOF_VERSION: u8 = {pin['proof_version']};",
        "current proof version changed",
    )
    require(
        node,
        f"pub const NODE_OUTPUTS: usize = {pin['outputs']};",
        "two-output statement shape changed",
    )
    require(
        node,
        """
        pub fn prove_one_input_transfer(
            asset_id: &AssetId,
            input: &(Coin, OwnerSecret),
            outputs: &[Coin; NODE_OUTPUTS],
            predecessor: &CoinProof,
            selector: usize,
        ) -> Result<CoinProof, NodeError>
        """,
        "one-input/one-predecessor API changed",
    )
    require(
        node,
        """
        enforce_sum_eq(
            &mut builder,
            [&input_value, &zero_value],
            [&output_values[0], &output_values[1]],
        )?;
        """,
        "one-input plus zero equals recipient plus change constraint changed",
    )
    require(
        node,
        """
        statement.extend_from_slice(&nullifier);
        for _ in 0..DIGEST_ELEMS {
            statement.push(ExprId::ZERO);
        }
        for commitment in &output_commitments {
            statement.extend_from_slice(commitment);
        }
        """,
        "in-circuit real-nullifier/zero-padding/output order changed",
    )
    require(
        node,
        """
        nullifiers: [nullifier, Digest::from_bytes([0u8; 32])],
        output_commitments: [outputs[0].commitment(), outputs[1].commitment()],
        """,
        "native v4 statement projection changed",
    )
    require(
        node,
        f"+ {pin['distinct_selector_bits']}; // 111",
        "two-input distinctness witness width changed",
    )
    require(
        node,
        """
        enforce_distinct_digest(
            &mut builder,
            &in_commitments[0],
            &in_commitments[1],
            witness.distinct_limb_bits,
        );
        """,
        "two-input in-circuit distinctness constraint changed",
    )
    require(
        node,
        """
        let selected = builder.select(selector_bits[2], quartet[1], quartet[0]);
        let one = const_expr(builder, BabyBear::ONE);
        let inverse = builder.div(one, selected);
        let check = builder.mul(selected, inverse);
        builder.connect(check, one);
        """,
        "selected unequal-limb inversion constraint changed",
    )
    require(
        node,
        """
        version == COIN_PROOF_VERSION
            || (version == LEGACY_COIN_PROOF_VERSION && mode == NodeMode::Mint)
        """,
        "legacy recursive predecessor policy changed",
    )
    require(
        accept,
        """
        if !root_lineage_is_current(coin.version) {
            return false;
        }
        """,
        "production current-root boundary changed",
    )
    require(
        node,
        "fn digest_distinctness_is_an_in_circuit_constraint()",
        "in-circuit distinctness adversarial receipt changed",
    )
    require(
        node,
        "fn legacy_recursive_policy_allows_only_ancestor_free_mints()",
        "legacy recursive policy receipt changed",
    )
    require(
        accept,
        "fn production_accepts_only_the_current_root_lineage()",
        "production root-version receipt changed",
    )
    require(
        security,
        f'pub const COIN_VK_TAG: &[u8] = b"{pin["vk_tag"]}";',
        "fail-closed verifier-set tag changed",
    )
    require(
        tests,
        f"assert_eq!(LEGACY_COIN_PROOF_VERSION, {pin['legacy_proof_version']});",
        "Rust version-boundary adversarial receipt changed",
    )
    require(
        tests,
        f"assert_eq!(COIN_PROOF_VERSION, {pin['proof_version']});",
        "Rust current-version receipt changed",
    )
    require(
        digest,
        f"pub const BABY_BEAR_P: u32 = {pin['baby_bear_modulus_hex']};",
        "BabyBear wire modulus changed",
    )
    require(
        digest,
        """
        .all(|chunk| u32::from_le_bytes(chunk.try_into().expect("4-byte chunk")) < BABY_BEAR_P)
        """,
        "strict eight-limb canonical digest check changed",
    )
    require(
        digest,
        "non-canonical digest: a little-endian u32 limb is >= BabyBear p",
        "non-canonical serde rejection changed",
    )
    require(
        digest,
        """
        let candidate: u32 = rng.random();
        if candidate < BABY_BEAR_P {
            break candidate;
        }
        """,
        "uniform rejection-sampled canonical randomness changed",
    )
    require(
        cli_ops,
        "Digest::random_canonical()",
        "CLI canonical randomness delegation changed",
    )
    require(
        ffi_wallet,
        "Digest::random_canonical()",
        "FFI canonical randomness delegation changed",
    )
    require(
        account,
        f"const SCHEMA_VERSION: u32 = {pin['account_config_generation']};",
        "Test USD account generation changed",
    )
    require(
        account,
        f"const CHECKPOINT_VERSION: u32 = {pin['checkpoint_version']};",
        "Test USD checkpoint generation changed",
    )
    require(
        account,
        f'pub const TEST_USD_V2_DEPLOYMENT_ID: &str = "{pin["deployment_id"]}";',
        "Test USD deployment id changed",
    )

    receipt = {
        "status": "verified",
        "rust_commit": actual,
        "proof_version": pin["proof_version"],
        "legacy_proof_version": pin["legacy_proof_version"],
        "real_nullifiers": 1,
        "padding_nullifier": 0,
        "outputs": pin["outputs"],
        "distinct_selector_bits": pin["distinct_selector_bits"],
        "legacy_recursive_policy": pin["legacy_recursive_policy"],
        "production_root_version": pin["proof_version"],
        "conservation": "input + zero = recipient + change",
        "vk_tag": pin["vk_tag"],
        "baby_bear_modulus": pin["baby_bear_modulus"],
        "canonical_digest_limbs": 8,
        "account_config_generation": pin["account_config_generation"],
        "checkpoint_version": pin["checkpoint_version"],
        "deployment_id": pin["deployment_id"],
        "scope": "source correspondence; Lean proves protocol semantics, not Rust/AIR equivalence",
    }
    print(json.dumps(receipt, sort_keys=True))


if __name__ == "__main__":
    try:
        main()
    except (OSError, subprocess.CalledProcessError, json.JSONDecodeError) as error:
        print(f"v4 Rust correspondence failed: {error}", file=sys.stderr)
        raise SystemExit(1) from error
