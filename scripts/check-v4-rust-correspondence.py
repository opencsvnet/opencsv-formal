#!/usr/bin/env python3
"""Fail closed if the pinned Rust v4 statement shape drifts from Lean.

This is deliberately a source-correspondence gate, not a Rust or AIR proof.
Lean proves the protocol semantics of the shape in OpenCsv/Forward.lean; this
script makes CI check that the exact pinned Rust source still exposes that
shape before the two artifacts are described as corresponding.
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
    security = (rust / "crates/opencsv-pcd/src/security.rs").read_text()
    tests = (rust / "crates/opencsv-pcd/tests/node.rs").read_text()

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

    receipt = {
        "status": "verified",
        "rust_commit": actual,
        "proof_version": pin["proof_version"],
        "legacy_proof_version": pin["legacy_proof_version"],
        "real_nullifiers": 1,
        "padding_nullifier": 0,
        "outputs": pin["outputs"],
        "conservation": "input + zero = recipient + change",
        "vk_tag": pin["vk_tag"],
        "scope": "source correspondence; Lean proves protocol semantics, not Rust/AIR equivalence",
    }
    print(json.dumps(receipt, sort_keys=True))


if __name__ == "__main__":
    try:
        main()
    except (OSError, subprocess.CalledProcessError, json.JSONDecodeError) as error:
        print(f"v4 Rust correspondence failed: {error}", file=sys.stderr)
        raise SystemExit(1) from error
