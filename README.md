# KNS Prover (Kerrigan NameSpace ZK Prover)

**KNS Prover** is a Zero-Knowledge (ZK) state-transition prover for **Kerrigan NameSpace (KNS)**. It executes batch validation of off-chain domain updates inside a zero-knowledge Virtual Machine (zkVM) and generates succinct cryptographic proofs (Groth16 SNARKs) to update domain state roots securely on-chain.

---

## 📌 Overview & Functionality

The KNS Prover processes batches of domain transactions, verifying all cryptographic and state transition rules off-chain before committing state changes to the blockchain.

### Supported Operations
- **`REG` (Register)**: Initial registration of a domain mapped to a Kerrigan Sapling shielded target address (`ks1...` on mainnet, `ktestsapling1...` on testnet) and an Ed25519 public key.
- **`UPD` (Update)**: Updating target addresses for existing domains.
- **`CHG` (Change Owner)**: Transferring domain ownership to a new Ed25519 public key.
- **`LST` (List)**: Listing a domain for sale on the marketplace at a specified price.
- **`ULT` (Unlist)**: Removing a domain listing from the marketplace.
- **`BUY` (Buy)**: Purchasing a listed domain and transferring ownership.

### What the Guest Program (`program`) Does
For each transaction in a batch, the guest program running inside the zkVM strictly enforces:
1. **Replay Protection**: Verifies sequential nonces (`nonce > old_nonce`).
2. **Input Validation**: Ensures valid domain string rules (TLDs `.kerrigan`, `.krgn`, `.private`, `.secure` and `.safe`) and Kerrigan Sapling address formats (bech32m) for the network the build targets.
3. **Cryptographic Signatures**: Validates Ed25519 signatures of domain owners.
4. **State Transition Integrity**: Validates and updates leaf nodes in a 128-level Sparse Merkle Tree (SMT). Leaf and internal-node hashes are domain-separated by a `0x00` / `0x01` tag prefix, so a leaf preimage can never be reinterpreted as an internal node. **The host that builds the tree must apply the identical tags**, including when deriving its empty-subtree constant ladder (`E₀ = 0×32`, `E₍ᵢ₊₁₎ = SHA256(0x01 ‖ Eᵢ ‖ Eᵢ)`).
5. **ABI Commit**: Encodes and commits the initial root (`old_root`), final root (`new_root`), and target block height (`end_block_height`) as public values.

---

## 🛠 Tech Stack & Dependencies

- **[Succinct SP1](https://github.com/succinctlabs/sp1)**: A performant 100% open-source zero-knowledge virtual machine (zkVM) that executes arbitrary Rust code compiled to RISC-V.
- **Zero-Knowledge Proofs (Groth16 SNARKs)**: Utilizes SP1's proof generation capabilities to produce succinct Groth16 proofs suitable for cost-effective EVM verification.
- **[Alloy](https://github.com/alloy-rs/alloy)**: Solidity type definitions and ABI encoding/decoding for EVM interoperability.
- **Ed25519 & SHA-256**: Acceleration for signature verification and Merkle tree hashing inside the zkVM.

---

## 🔗 Smart Contract Integration & Trustless State

The KNS Prover operates in tandem with the **EVM anchor contract**:  
👉 **[alexxiy/kerrigan-namespace-evm-anchor](https://github.com/alexxiy/kerrigan-namespace-evm-anchor)**

### How Trustlessness is Achieved
1. **Off-Chain Execution, On-Chain Verification**: Sequencers bundle domain transactions off-chain and run the KNS Prover script to generate a Groth16 SNARK proof along with public outputs (`old_root`, `new_root`).
2. **Cryptographic Proof Verification**: The proof and public values are submitted to the EVM anchor contract. The contract verifies the proof via the SP1 Verifier contract on-chain.
3. **What the proof guarantees**: The smart contract does not have to re-execute the batch or scan Kerrigan. Given the inputs supplied, the proof mathematically guarantees that:
   - All transactions inside the batch were validly signed by their respective owners.
   - The state root transition from `old_root` to `new_root` strictly follows protocol rules without state corruption.
   - No invalid registrations, double-spends, or unauthorized domain transfers occurred.

4. **What the proof does *not* guarantee — and what covers it**: the proof says nothing about whether those inputs were the *real* command stream. A registrar could prove a perfectly valid transition over a censored or invented set of commands. That half is covered by **public replication, not cryptography**:

   - Every command is a shielded note sent to the registrar's protocol address, with the payment as its value and the signed command in its 512-byte Sapling memo — atomically bound.
   - The registrar **publishes the viewing key for that address**, so anyone can decrypt the entire command history from genesis, in canonical chain order.
   - The indexer is open source and deterministic, so any third party replays that history, computes the SMT root independently, and compares it with the root anchored on-chain.

   A registrar that censors, invents, mis-credits or reorders produces a root that every independent indexer contradicts. The system is therefore **fraud-evident**: deviation is detectable by anyone without permission, though a bad batch can land on-chain and be contradicted afterwards rather than being prevented outright.

> [!NOTE]
> Payments *in* are fully auditable this way. What the registrar *sends* — seller payouts
> and losing-bidder refunds — is not, not even in total: Kerrigan Core puts no outgoing
> viewing key on outputs it pays to others, and returns the change to an internal key the
> published viewing key does not cover. The viewing key shows when the registrar spends a
> note, not where its value went. See the trust-model section of `CLAUDE.md`.

### Verification Key (`vKey`) & On-Chain Connection
- **What is a `vKey`?** When the guest program code (`program`) is compiled into a RISC-V ELF binary, SP1 computes a unique cryptographic 32-byte identifier called the **Program Verification Key (`vKey`)**. Any modification to the guest logic, dependencies, or code will alter this `vKey`.
- **Connecting to Smart Contract**: The anchor contract stores this exact `programVKey` on-chain. When a proof is submitted, the on-chain SP1 Verifier contract checks that the proof was generated specifically by the program matching this registered `vKey`. If a registrar attempts to run modified or malicious program code, the generated proof will be bound to a different `vKey` and rejected by the smart contract.

### Proving Open-Source Immutability (Reproducible Builds)
- Anyone can audit and verify that the registrar is running the exact, untampered open-source code from this repository.
- By running a deterministic Docker build (`cargo prove build --docker --tag v6.9.0`), SP1 compiles the Rust guest code inside a standardized environment, producing an identical RISC-V ELF binary and `vKey` anywhere. The steps, and why both the Docker image and its tag matter, are in [Verifying the vKey](#verifying-the-vkey).
- Comparing your locally compiled `vKey` with the `programVkey()` registered in the anchor contract mathematically proves that the deployed, active prover on the registrar side corresponds 1:1 with this open-source code.

---

## 📁 Repository Structure

```
├── kns-core/           # Shared protocol logic (the wire format's single source of truth)
│   ├── Cargo.toml
│   └── src/lib.rs     # Batch structs, leaf/node hashing, SMT, signed messages, validation
│                      # + golden-vector tests a host implementation must reproduce
├── program/           # ZK Guest Program (runs inside SP1 zkVM)
│   ├── Cargo.toml
│   └── src/main.rs    # Per-operation invariants & state transition driver
├── script/            # Host Prover Executable (CLI script)
│   ├── Cargo.toml
│   └── src/main.rs    # SP1 Prover Client runner & proof generator
├── Cargo.toml         # Workspace manifest with SP1 patched cryptographic crates
└── README.md
```

### Interoperating with the host

Anything both the prover and the host (the PHP backend, a signing wallet) must agree
on byte-for-byte lives in **`kns-core`** — the batch structures, the exact bytes that
get signed for each operation, the leaf and node hash functions, and the Merkle path
traversal order. It was previously duplicated between the guest and the runner.

`kns-core` ships golden-vector tests covering the leaf hash, the empty-subtree
ladder, the path bit-ordering and all six signed-message formats. **A host
implementation should reproduce every one of those values.** If it cannot, the two
sides disagree and proofs will not verify:

```bash
cargo test -p kns-core
```

### Network builds

The protocol is parameterised at compile time:

| Build | Message prefix | Accepted addresses | vKey |
|:---|:---|:---|:---|
| default | `KNS:1:` | mainnet Sapling (`ks1…`, 78 chars, bech32m) | mainnet |
| `--features testnet` | `tKNS:1:` | testnet Sapling (`ktestsapling1…`, 88 chars, bech32m) | distinct |

Because the prefix is compiled into the guest ELF, the two networks get different
vKeys, so a testnet proof cannot be submitted to the mainnet contract — and a
signature produced against a testnet deployment can never be replayed onto mainnet.

---

## 🚀 Usage

### Requirements
- **Rust toolchain** (compatible with SP1)
- **SP1 toolchain (`sp1up`)** installed
- **Docker**, or Podman with a `docker` alias, to reproduce the `vKey` (see below)

### Building the Guest Program
To compile the zkVM guest program into ELF format, navigate to the `program` directory:
```bash
cd program
cargo prove build
```

For deterministic/reproducible builds using Docker (to verify `vKey` matching):
```bash
cd program
cargo prove build --docker --tag v6.9.0
```

> [!NOTE]
> The guest ELF — and therefore the `vKey` — is compiled by the SP1 `succinct`
> toolchain installed by `sp1up`, **not** by the toolchain named in `/rust-toolchain`
> (which governs only the host `script` build). `vKey` reproducibility depends on the
> SP1 toolchain version, the committed `Cargo.lock`, the guest source, and the path of
> the cargo home the guest's dependencies are built from. Use `--docker` with `--tag` to
> pin all of them at once.

### Verifying the vKey

Build the guest in SP1's Docker image from the commit you want to check, then print its
`vKey`:

```bash
git checkout v0.1.0            # or a release from the table below, with its --tag (see below)
cd program
cargo prove build --docker --tag v6.9.0
cargo prove vkey --elf ../target/elf-compilation/docker/riscv64im-succinct-zkvm-elf/release/kns-program
```

`cargo prove vkey` prints `Verification Key Hash:` and the `vKey`. For a testnet build, add
`--features testnet` to the build; it gives a different `vKey`.

| Source | `vKey` (mainnet) | On the anchor contract |
|:---|:---|:---|
| `v0.1.0` | set by the release build | `programVkey()` in epoch 1, from the contract's deployment |

Compare with the anchor contract on BNB Smart Chain (its address is in the
`kerrigan-namespace-evm-anchor` README once deployed):

- `programVkey()` (selector `0x09665ee7`): the `vKey` in force now.
- `pendingRulesVkey()` (selector `0x78aa4dbf`): the `vKey` of a proposed rules change, or zero
  when there is none. A rules change is timelocked, and `rulesChangeActivatesAt()` (selector
  `0x90b86556`, a Unix time; zero until the change is approved) says when it can take effect.
  Check the new `vKey` before then.
- `epoch()` (selector `0x900cf0cf`): the epoch in force. It goes up by one whenever a rules
  change activates or the root is rolled back, so the table above names the epoch of each
  `vKey`.

```bash
curl -s -X POST https://bsc-dataseed.bnbchain.org -H 'Content-Type: application/json' \
  -d '{"jsonrpc":"2.0","id":1,"method":"eth_call","params":[{"to":"<anchor contract address>","data":"0x09665ee7"},"latest"]}'
```

**Why the Docker image.** The guest ELF contains the absolute paths of the crates it was
compiled from: panic locations in `sp1-zkvm`, `embedded-alloc`, `bech32` and the patched
`curve25519-dalek`. So the path of your cargo home is part of the ELF, and of the `vKey`.
The image builds with its cache at `/root/.cargo`, the same path on every machine.

A native build (`cargo prove build` without `--docker`) reproduces the `vKey` only if your
cargo home is `/root/.cargo` and `sp1up` installed the same toolchain as the image (the SP1
version in `Cargo.lock`). Tested on one machine with the same source and the same SP1
toolchain:

| Changed | `vKey` |
|:---|:---|
| the workspace path | same |
| the cargo cache emptied (same path) | same |
| `CARGO_HOME` moved elsewhere | different |

A `vKey` that differs after a native build is therefore not evidence of a mismatch;
rebuild with Docker.

**Why `--tag`.** The image carries the guest compiler. Without `--tag`, `cargo prove` uses
the image matching the `cargo-prove` you have installed, so a different SP1 install can
bring a different compiler. The tag to use is `v` followed by the `sp1-build` version in
`Cargo.lock` of the commit you build: `v6.9.0` for `v0.1.0`.

### Running the Prover

The prover is invoked per batch. It reads `{batch_id}_batch.json` from `--batch-dir`
and writes its outputs alongside it.

Validate a batch cheaply, without paying for proving (reports the zkVM cycle count):
```bash
cargo run --release -- --batch-dir /path/to/batches --batch-id 42 --execute
```

Generate the Groth16 proof for on-chain submission:
```bash
cargo run --release -- --batch-dir /path/to/batches --batch-id 42
```

Set the proving backend via `SP1_PROVER` (see `.env.example`). The `mock` and `light`
modes cannot produce an on-chain-verifiable proof and are rejected unless
`--allow-mock` is passed; even then `{batch_id}_result.json` is withheld so a
sequencer can never submit an unusable proof.

#### Outputs

| File | Written when | Purpose |
|:---|:---|:---|
| `{batch_id}_proof.bin` | proof generated | Groth16 proof bytes for the EVM verifier |
| `{batch_id}_public_values.bin` | proof generated | ABI-encoded `(old_root, new_root, end_block_height)` |
| `{batch_id}_result.json` | proof generated **and** verified locally | The sequencer's "ready to submit" signal |
| `{batch_id}_debug.log` | always | Full trace log (appends across reruns) |
| `{batch_id}_error.txt` | on failure | The reason the batch failed |

#### Exit codes

| Code | Meaning |
|:---|:---|
| `0` | Success |
| `1` | Run failed — `{batch_id}_error.txt` contains the reason |
| `2` | Bad invocation — `--batch-dir`/`--batch-id` failed to parse, so no error file could be written. Details on stderr. |
