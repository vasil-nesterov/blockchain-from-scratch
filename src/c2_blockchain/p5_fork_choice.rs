// TODO : run without custom .best_chain implementations

//! Forks in the blockchain represent alternative histories of the system.
//! When forks arise in the blockchain, users need a way to decide which chain
//! they will consider best, for now. This is known as a "fork choice rule".
//! There are several meaningful notions of "best", so we introduce a trait
//! that allows multiple implementations.
//!
//! Since we have nothing to add to the Block or Header data structures in this lesson,
//! we will import them from the previous lesson.

use core::num;
use std::u64;

use rand::random;

use super::{
    p3_consensus::THRESHOLD,
    p4_batched_extrinsics::{Block, Header},
};
use crate::hash;

/// Judge which blockchain is "best" when there are multiple candidates. There are several
/// meaningful notions of "best" which is why this is a trait instead of just a
/// method.
pub trait ForkChoice {
    /// Compare two chains, and return the "best" one.
    ///
    /// The chains are not assumed to start from the same genesis block, or even a
    /// genesis block at all. This makes it possible to compare entirely disjoint
    /// histories. It also makes it possible to compare _only_ the divergent part
    /// of sibling chains back to the last common ancestor.
    ///
    /// The chains are assumed to be valid, so it is up to the caller to check
    /// validity first if they are unsure.
    fn first_chain_is_better(chain_1: &[Header], chain_2: &[Header]) -> bool;

    /// Compare many chains and return the best one.
    ///
    /// It is always possible to compare several chains if you are able to compare
    /// two chains. Therefore this method has a provided implementation. However,
    /// it may be much more performant to write a fork-choice-specific implementation.
    fn best_chain<'a>(candidate_chains: &[&'a [Header]]) -> &'a [Header] {
        let mut best_chain_so_far = candidate_chains[0];

        for i in 1..candidate_chains.len() {
            if Self::first_chain_is_better(candidate_chains[i], &best_chain_so_far) {
                best_chain_so_far = candidate_chains[i];
            }
        }

        best_chain_so_far
    }
}

/// The "best" chain is simply the longest chain.
pub struct LongestChainRule;

impl ForkChoice for LongestChainRule {
    fn first_chain_is_better(chain_1: &[Header], chain_2: &[Header]) -> bool {
        chain_1.len() > chain_2.len()
    }

    fn best_chain<'a>(candidate_chains: &[&'a [Header]]) -> &'a [Header] {
        // Remember, this method is provided. You _can_ solve the exercise by
        // simply deleting this block. It is up to you to decide whether this fork
        // choice warrants a custom implementation.
        candidate_chains
            .iter()
            .max_by(|a, b| a.len().cmp(&b.len()))
            .expect("candidate_chains to contain at least 1 chain")
    }
}

/// The best chain is the one with the most accumulated work.
///
/// In Proof of Work chains, each block contains a certain amount of "work".
/// Roughly speaking, the lower a block's hash is, the more work it contains,
/// because finding a block with a low hash requires, on average, trying more
/// nonces. Modeling the amount of work required to achieve a particular hash
/// is out of scope for this exercise, so we will use the not-really-right-but
/// conceptually-good-enough formula `work = THRESHOLD - block_hash`
pub struct HeaviestChainRule;

/// Mutates a block (and its embedded header) to contain more PoW difficulty.
/// This will be useful for exploring the heaviest chain rule. The expected
/// usage is that you create a block using the normal `Block.child()` method
/// and then pass the block to this helper for additional mining.
fn mine_extra_hard(block: &mut Block, threshold: u64) {
    let header = &mut block.header;

    while hash(header) > threshold {
        header.consensus_digest = random();
    }
}

// Useful for `create_fork_one_side_longer_other_side_heavier' exercise
fn mine_header_extra_hard(header: &mut Header, threshold: u64) {
    while hash(header) > threshold {
        header.consensus_digest = random();
    }
}

fn mine_header_not_too_hard(header: &mut Header, threshold: u64) {
    while hash(header) < threshold {
        header.consensus_digest = random();
    }
}

fn chain_weight(chain: &[Header]) -> u128 {
    chain.iter().map(|h| hash(h) as u128).sum()
}

impl ForkChoice for HeaviestChainRule {
    fn first_chain_is_better(chain_1: &[Header], chain_2: &[Header]) -> bool {
        chain_weight(chain_1) < chain_weight(chain_2)
    }

    fn best_chain<'a>(candidate_chains: &[&'a [Header]]) -> &'a [Header] {
        candidate_chains
            .iter()
            .min_by(|a, b| chain_weight(a).cmp(&chain_weight(b)))
            .expect("candidate_chains to contain at least 1 chain")
    }
}
/// The best chain is the one with the most blocks that have even hashes.
///
/// This exact rule is a bit contrived, but it does model a family of fork choice rules
/// that are useful in the real world. We just can't code them here because we haven't
/// implemented Proof of Authority yet. Consider the following real world examples
/// that have very similar implementations.
///
/// 1. Secondary authors. In each round there is one author who is supposed to author.
///    If that author fails to create a block, there is a secondary author who may do so.
///    The best chain is the one with the most primary-authored blocks.
///
/// 2. Interleaved Pow/PoA. In each round there is one author who is allowed to author.
///    Anyone else is allowed to mine a PoW-style block. The best chain is the one with
///    the most PoA blocks, and ties are broken by the most accumulated work.
pub struct MostBlocksWithEvenHash;

fn number_of_even_blocks(chain: &[Header]) -> u64 {
    chain.iter().filter(|h| hash(h) % 2 == 0).count() as u64
}

impl ForkChoice for MostBlocksWithEvenHash {
    fn first_chain_is_better(chain_1: &[Header], chain_2: &[Header]) -> bool {
        number_of_even_blocks(chain_1) > number_of_even_blocks(chain_2)
    }

    fn best_chain<'a>(candidate_chains: &[&'a [Header]]) -> &'a [Header] {
        candidate_chains
            .iter()
            .max_by(|a, b| number_of_even_blocks(a).cmp(&number_of_even_blocks(b)))
            .expect("candidate_chains to contain at least 1 chain")
    }
}

// This lesson has omitted one popular fork choice rule:
// GHOST - Greedy Heaviest Observed SubTree
//
// I've omitted GHOST from here because it requires information about blocks that
// are _not_ in the chain to decide which chain is best. Therefore it does't work
// well with this relatively simple trait definition. We will return to the GHOST
// rule later when we have written a full blockchain client
//
// The GHOST rule was first published in 2013 by Yonatan Sompolinsky and Aviv Zohar.
// Learn more at https://eprint.iacr.org/2013/881.pdf

//

/// Build and return two different chains with a common prefix.
/// They should have the same genesis header. Both chains should be valid.
/// The first chain should be longer (have more blocks), but the second
/// chain should have more accumulated work.
///
/// Return your solutions as three vectors:
/// 1. The common prefix including genesis
/// 2. The suffix chain which is longer (non-overlapping with the common prefix)
/// 3. The suffix chain with more work (non-overlapping with the common prefix)
fn create_fork_one_side_longer_other_side_heavier() -> (Vec<Header>, Vec<Header>, Vec<Header>) {
    let custom_threshold = u64::max_value() / 1_000;

    let g = Header::genesis();
    let common_1 = g.child(hash(&[1]), 1);
    let common_2 = common_1.child(hash(&[2]), 2);

    let mut longer_3 = common_2.child(hash(&[3]), 3);
    mine_header_not_too_hard(&mut longer_3, custom_threshold);
    let mut longer_4 = longer_3.child(hash(&[4]), 4);
    mine_header_not_too_hard(&mut longer_4, custom_threshold);
    let mut longer_5 = longer_4.child(hash(&[5]), 5);
    mine_header_not_too_hard(&mut longer_5, custom_threshold);

    let mut heavier_3 = common_2.child(hash(&[6]), 6);
    mine_header_extra_hard(&mut heavier_3, custom_threshold);
    let mut heavier_4 = heavier_3.child(hash(&[7]), 7);
    mine_header_extra_hard(&mut heavier_4, custom_threshold);

    (
        vec![g, common_1, common_2],
        vec![longer_3, longer_4, longer_5],
        vec![heavier_3, heavier_4],
    )
}

#[test]
fn bc_5_longest_chain() {
    let g = Header::genesis();

    let h_a1 = g.child(hash(&[1]), 1);
    let h_a2 = h_a1.child(hash(&[2]), 2);
    let chain_1 = &[g.clone(), h_a1, h_a2];

    let h_b1 = g.child(hash(&[3]), 3);
    let chain_2 = &[g, h_b1];

    assert!(LongestChainRule::first_chain_is_better(chain_1, chain_2));

    assert_eq!(LongestChainRule::best_chain(&[chain_1, chain_2]), chain_1);
}

#[test]
fn bc_5_mine_to_custom_difficulty() {
    let g = Block::genesis();
    let mut b1 = g.child(vec![1, 2, 3]);

    // We want the custom threshold to be high enough that we don't take forever mining
    // but low enough that it is unlikely we accidentally meet it with the normal
    // block creation function
    let custom_threshold = u64::max_value() / 1000;
    mine_extra_hard(&mut b1, custom_threshold);

    assert!(hash(&b1.header) < custom_threshold);
}

#[test]
fn bc_5_heaviest_chain() {
    let g = Header::genesis();

    let custom_threshold = u64::max_value() / 1000;

    let mut i = 0;
    let h_a1 = loop {
        let header = g.child(hash(&[i]), i);
        // Extrinsics root hash must be higher than threshold (less work done)
        if hash(&header) > custom_threshold {
            break header;
        }
        i += 1;
    };
    let chain_1 = &[g.clone(), h_a1];

    let h_b1 = loop {
        let header = g.child(hash(&[i]), i);
        // Extrinsics root hash must be lower than threshold (more work done)
        // If it's lower than thresho
        if hash(&header) < custom_threshold {
            break header;
        }
        i += 1;
    };
    let chain_2 = &[g, h_b1];

    assert!(HeaviestChainRule::first_chain_is_better(chain_2, chain_1));

    assert_eq!(HeaviestChainRule::best_chain(&[chain_1, chain_2]), chain_2);
}

#[test]
fn bc_5_most_even_blocks() {
    let g = Header::genesis();

    let mut h_a1 = g.child(2, 0);
    for i in 0..u64::max_value() {
        h_a1 = g.child(2, i);
        if hash(&h_a1) % 2 == 0 {
            break;
        }
    }
    let mut h_a2 = g.child(2, 0);
    for i in 0..u64::max_value() {
        h_a2 = h_a1.child(2, i);
        if hash(&h_a2) % 2 == 0 {
            break;
        }
    }
    let chain_1 = &[g.clone(), h_a1, h_a2];

    let mut h_b1 = g.child(2, 0);
    for i in 0..u64::max_value() {
        h_b1 = g.child(2, i);
        if hash(&h_b1) % 2 != 0 {
            break;
        }
    }
    let mut h_b2 = g.child(2, 0);
    for i in 0..u64::max_value() {
        h_b2 = h_b1.child(2, i);
        if hash(&h_b2) % 2 != 0 {
            break;
        }
    }
    let chain_2 = &[g, h_b1, h_b2];

    assert!(MostBlocksWithEvenHash::first_chain_is_better(
        chain_1, chain_2
    ));

    assert_eq!(
        MostBlocksWithEvenHash::best_chain(&[chain_1, chain_2]),
        chain_1
    );
}

#[test]
fn bc_5_longest_vs_heaviest() {
    let (_, longest_chain, pow_chain) = create_fork_one_side_longer_other_side_heavier();

    assert!(LongestChainRule::first_chain_is_better(
        &longest_chain,
        &pow_chain
    ));

    assert_eq!(
        LongestChainRule::best_chain(&[&longest_chain, &pow_chain]),
        &longest_chain
    );

    let (_, longest_chain, pow_chain) = create_fork_one_side_longer_other_side_heavier();

    assert!(HeaviestChainRule::first_chain_is_better(
        &pow_chain,
        &longest_chain
    ));

    assert_eq!(
        HeaviestChainRule::best_chain(&[&longest_chain, &pow_chain]),
        &pow_chain
    );
}
