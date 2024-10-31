//! Until now, each block has contained just a single extrinsic. Really we would prefer to batch them.
//! Now, we stop relying solely on headers, and instead, create complete blocks.

use rand::random;

use crate::hash;
type Hash = u64;
use super::p3_consensus::THRESHOLD;

/// The header no longer contains an extrinsic directly. Rather a vector of extrinsics will be stored in
/// the block body.
/// We apply previous learnings in consensus but move away from Political or Arbitrary rules and focus on proof of work.
/// Recall: for Proof of Work the consensus digest is a nonce which gets the block hash below a certain threshold.
/// We are still storing the state in the header for now. This will change in an upcoming
/// lesson as well.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Header {
    parent: Hash,
    height: u64,
    // We now switch from storing an extrinsic directly, to storing an extrinsic root.
    // This is basically a concise cryptographic commitment to the complete list of extrinsics.
    // For example, a hash or a Merkle root.
    extrinsics_root: Hash,
    state: u64,
    pub consensus_digest: u64,
}

// Methods for creating and verifying headers.
//
// With the extrinsics no longer stored in the header, we can no longer do
// "on-chain" execution with just headers. That means that this code actually
// gets simpler in many ways. All the old execution logic, plus some new batching
// logic moves to the block level now.
impl Header {
    /// Returns a new valid genesis header.
    pub fn genesis() -> Self {
        Header {
            parent: 0,
            height: 0,
            extrinsics_root: hash::<Vec<u64>>(&Vec::new()),
            state: 0,
            consensus_digest: 0,
        }
    }

    /// Create and return a valid child header.
    /// Without the extrinsics themselves, we cannot calculate the final state
    /// so that information is passed in.
    pub fn child(&self, extrinsics_root: Hash, state: u64) -> Self {
        let mut header = Header {
            parent: hash(self),
            height: self.height + 1,
            extrinsics_root,
            state,
            consensus_digest: 0,
        };

        while hash(&header) > THRESHOLD {
            header.consensus_digest = random();
        }

        header
    }

    /// Verify a single child header.
    ///
    /// This is a slightly different interface from the previous units. Rather
    /// than verify an entire sub-chain, this function checks a single header.
    /// This is useful because checking the header can now be thought of as a
    /// subtask of checking an entire block. So it doesn't make sense to check
    /// the entire header chain at once if the chain may be invalid at the second block.
    fn verify_child(&self, child: &Header) -> bool {
        child.parent == hash(self) && child.height == self.height + 1 && hash(child) <= THRESHOLD
    }

    /// Verify that all the given headers form a valid chain from this header to the tip.
    ///
    /// We can now trivially write the old verification function in terms of the new one.
    /// Extra street cred if you can write it
    ///  - [x] with a loop
    ///  - [x] with head recursion
    ///  - [x] with tail recursion
    fn verify_sub_chain(&self, chain: &[Header]) -> bool {
        self.verify_sub_chain_for_tail_rec(chain)
    }

    fn verify_sub_chain_for_tail_rec(&self, chain: &[Header]) -> bool {
        fn verify_sub_chain_for_tail_rec_inner(
            parent: &Header,
            chain: &[Header],
            acc: bool,
        ) -> bool {
            match chain.split_first() {
                Some((child, tail)) => verify_sub_chain_for_tail_rec_inner(
                    child,
                    tail,
                    acc && parent.verify_child(child),
                ),
                None => acc,
            }
        }

        verify_sub_chain_for_tail_rec_inner(self, chain, true)
    }

    fn verify_sub_chain_for_head_rec(&self, chain: &[Header]) -> bool {
        match chain.split_first() {
            Some((head, tail)) => {
                head.verify_sub_chain_for_head_rec(tail) && self.verify_child(head)
            }
            None => true,
        }
    }

    fn verify_sub_chain_loop(&self, chain: &[Header]) -> bool {
        let mut i = 0;
        let mut previous = self;

        while i < chain.len() {
            if !previous.verify_child(&chain[i]) {
                return false;
            }

            previous = &chain[i];
            i += 1;
        }

        true
    }

    fn verify_sub_chain_for_in(&self, chain: &[Header]) -> bool {
        let mut previous_header = self;

        for next_header in chain.iter() {
            if previous_header.verify_child(next_header) {
                return false;
            }
            previous_header = next_header;
        }

        true
    }
}

/// A complete Block is a header and the extrinsics.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Block {
    pub(crate) header: Header,
    pub(crate) body: Vec<u64>,
}

// Methods for creating and verifying blocks.
//
// These methods are analogous to the methods on the headers. All of the
// transaction execution logic is now handled at the block level because
// the transactions are no longer available at the Header level.
impl Block {
    /// Returns a new valid genesis block. By convention this block has no extrinsics.
    pub fn genesis() -> Self {
        Block {
            header: Header::genesis(),
            body: Vec::new(),
        }
    }

    /// Create and return a valid child block.
    /// The extrinsics are batched now, so we need to execute each of them.
    pub fn child(&self, extrinsics: Vec<u64>) -> Self {
        let state: u64 = self.header.state + extrinsics.iter().sum::<u64>();
        let header = Header::child(&self.header, hash(&extrinsics), state);

        Block {
            header,
            body: extrinsics,
        }
    }

    /// Verify that all the given blocks form a valid chain from this block to the tip.
    ///
    /// We need to verify the headers as well as execute all transactions and check the final state.
    pub fn verify_sub_chain(&self, chain: &[Block]) -> bool {
        fn new_block_state_is_valid(previous: &Block, next: &Block) -> bool {
            next.header.state == previous.header.state + next.body.iter().sum::<u64>()
        }
        fn extrinsics_root_is_valid(block: &Block) -> bool {
            hash(&block.body) == block.header.extrinsics_root
        }

        chain
            .iter()
            .fold(
                (true, self),
                |(sub_chain_valid_so_far, previous_block): (bool, &Block), next_block| {
                    (
                        sub_chain_valid_so_far
                            && new_block_state_is_valid(previous_block, next_block)
                            && extrinsics_root_is_valid(next_block)
                            && previous_block.header.verify_child(&next_block.header),
                        next_block,
                    )
                },
            )
            .0
    }
}

/// Create an invalid child block of the given block. Although the child block is invalid,
/// the header should be valid.
///
/// Now that extrinsics are separate from headers, the logic for checking headers does
/// not include actual transaction execution. That means it is possible for a header to be
/// valid, but the block containing that header to be invalid.
///
/// Notice that you do not need the entire parent block to do this. You only need the header.
fn build_invalid_child_block_with_valid_header(parent: &Header) -> Block {
    Block {
        header: parent.child(123, 456),
        body: Vec::new(),
    }
}

#[test]
fn bc_4_genesis_header() {
    let g = Header::genesis();
    assert_eq!(g.height, 0);
    assert_eq!(g.parent, 0);
    assert_eq!(g.extrinsics_root, hash(&Vec::<u64>::new()));
    assert_eq!(g.state, 0);
    assert_eq!(g.consensus_digest, 0);
}

#[test]
fn bc_4_genesis_block() {
    let gh = Header::genesis();
    let gb = Block::genesis();

    assert_eq!(gb.header, gh);
    assert!(gb.body.is_empty());
}

#[test]
fn bc_4_child_block_empty() {
    let b0 = Block::genesis();
    let b1 = b0.child(vec![]);

    assert_eq!(b1.header.height, 1);
    assert_eq!(b1.header.parent, hash(&b0.header));
    assert_eq!(
        b1,
        Block {
            header: b1.header.clone(),
            body: vec![]
        }
    );
}

#[test]
fn bc_4_child_block() {
    let b0 = Block::genesis();
    let b1 = b0.child(vec![1, 2, 3, 4, 5]);

    assert_eq!(b1.header.height, 1);
    assert_eq!(b1.header.parent, hash(&b0.header));
    assert_eq!(
        b1,
        Block {
            header: b1.header.clone(),
            body: vec![1, 2, 3, 4, 5]
        }
    );
}

#[test]
fn bc_4_child_header() {
    let g = Header::genesis();
    let h1 = g.child(hash(&[1, 2, 3]), 6);

    assert_eq!(h1.height, 1);
    assert_eq!(h1.parent, hash(&g));
    assert_eq!(h1.extrinsics_root, hash(&[1, 2, 3]));
    assert_eq!(h1.state, 6);
    assert!(hash(&h1) < THRESHOLD);

    let h2 = h1.child(hash(&[10, 20]), 36);

    assert_eq!(h2.height, 2);
    assert_eq!(h2.parent, hash(&h1));
    assert_eq!(h2.extrinsics_root, hash(&[10, 20]));
    assert_eq!(h2.state, 36);
    assert!(hash(&h2) < THRESHOLD);
}

#[test]
fn bc_4_verify_three_blocks() {
    let g = Block::genesis();
    let b1 = g.child(vec![1]);
    let b2 = b1.child(vec![2]);
    let chain = vec![g.clone(), b1, b2];
    assert!(g.verify_sub_chain(&chain[1..]));
}

#[test]
fn bc_4_invalid_header_does_not_check() {
    let g = Header::genesis();
    let h1 = Header {
        parent: 0,
        height: 100,
        extrinsics_root: 0,
        state: 100,
        consensus_digest: 0,
    };

    assert!(!g.verify_child(&h1));
}

#[test]
fn bc_4_invalid_block_state_does_not_check() {
    let b0 = Block::genesis();
    let mut b1 = b0.child(vec![1, 2, 3]);
    b1.body = vec![];

    assert!(!b0.verify_sub_chain(&[b1]));
}

#[test]
fn bc_4_block_with_invalid_header_does_not_check() {
    let b0 = Block::genesis();
    let mut b1 = b0.child(vec![1, 2, 3]);
    b1.header = Header::genesis();

    assert!(!b0.verify_sub_chain(&[b1]));
}

#[test]
fn bc_4_student_invalid_block_really_is_invalid() {
    let gb = Block::genesis();
    let gh = &gb.header;

    let b1 = build_invalid_child_block_with_valid_header(gh);
    let h1 = &b1.header;

    // Make sure that the header is valid according to header rules.
    assert!(gh.verify_child(h1));

    // Make sure that the block is not valid when executed.
    assert!(!gb.verify_sub_chain(&[b1]));
}
