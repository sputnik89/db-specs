use vstd::prelude::*;

verus! {

pub type Key = Seq<char>;
pub type Rows = Seq<(Key, i32)>;
pub type AbstractDatabase = Map<Key, i32>;
pub type CallId = nat;
pub type ThreadId = nat;
pub type Time = nat;

pub open spec fn key_lt(a: Key, b: Key) -> bool
    decreases a.len(),
{
    if b.len() == 0 {
        false
    } else if a.len() == 0 {
        true
    } else if a[0] != b[0] {
        (a[0] as u32) < (b[0] as u32)
    } else {
        key_lt(a.drop_first(), b.drop_first())
    }
}

pub open spec fn key_le(a: Key, b: Key) -> bool {
    a == b || key_lt(a, b)
}

pub enum DatabaseOperation {
    Get(Key),
    Put(Key, i32),
    Scan(Key, Key),
    Sort,
}

pub enum DatabaseResult {
    Get(Option<i32>),
    Put,
    Scan(Rows),
    Sort(Rows),
}

pub open spec fn rows_strictly_sorted(rows: Rows) -> bool {
    forall|i: int, j: int| #![trigger rows[i], rows[j]]
        0 <= i < j < rows.len() ==> key_lt(rows[i].0, rows[j].0)
}

pub open spec fn rows_are_exact_range(
    contents: AbstractDatabase,
    lo: Key,
    hi: Key,
    rows: Rows,
) -> bool {
    &&& key_le(lo, hi)
    &&& rows_strictly_sorted(rows)
    &&& forall|i: int| #![trigger rows[i]] 0 <= i < rows.len() ==> {
        let key = rows[i].0;
        &&& key_le(lo, key)
        &&& key_le(key, hi)
        &&& contents.dom().contains(key)
        &&& contents[key] == rows[i].1
    }
    &&& forall|key: Key| #![trigger contents.dom().contains(key)]
        contents.dom().contains(key) && key_le(lo, key) && key_le(key, hi)
            ==> exists|i: int| #![trigger rows[i]]
                0 <= i < rows.len() && rows[i].0 == key
}

pub open spec fn rows_are_exact_database(
    contents: AbstractDatabase,
    rows: Rows,
) -> bool {
    &&& rows_strictly_sorted(rows)
    &&& forall|i: int| #![trigger rows[i]] 0 <= i < rows.len() ==> {
        let key = rows[i].0;
        &&& contents.dom().contains(key)
        &&& contents[key] == rows[i].1
    }
    &&& forall|key: Key| #![trigger contents.dom().contains(key)]
        contents.dom().contains(key) ==> exists|i: int| #![trigger rows[i]]
            0 <= i < rows.len() && rows[i].0 == key
}

// The sequential semantics reused by the concurrent history specification.
// Each position in a linearization witness must satisfy exactly one such step.
pub open spec fn database_step(
    pre: AbstractDatabase,
    operation: DatabaseOperation,
    result: DatabaseResult,
    post: AbstractDatabase,
) -> bool {
    match (operation, result) {
        (DatabaseOperation::Get(key), DatabaseResult::Get(value)) => {
            &&& post == pre
            &&& value == if pre.dom().contains(key) { Some(pre[key]) } else { None }
        },
        (DatabaseOperation::Put(key, value), DatabaseResult::Put) => {
            post == pre.insert(key, value)
        },
        (DatabaseOperation::Scan(lo, hi), DatabaseResult::Scan(rows)) => {
            &&& post == pre
            &&& rows_are_exact_range(pre, lo, hi, rows)
        },
        (DatabaseOperation::Sort, DatabaseResult::Sort(rows)) => {
            &&& post == pre
            &&& rows_are_exact_database(pre, rows)
        },
        _ => false,
    }
}

// One dynamically invoked operation. Calls from different threads may overlap:
// their [invoked_at, returned_at] intervals need not be disjoint.
pub struct CallRecord {
    pub thread: ThreadId,
    pub operation: DatabaseOperation,
    pub invoked_at: Time,
    pub returned_at: Option<Time>,
    pub result: Option<DatabaseResult>,
}

pub struct ConcurrentHistory {
    pub calls: Map<CallId, CallRecord>,
}

pub open spec fn completed(call: CallRecord) -> bool {
    call.returned_at.is_some() && call.result.is_some()
}

pub open spec fn call_well_formed(call: CallRecord) -> bool {
    match (call.returned_at, call.result) {
        (Some(returned_at), Some(_)) => call.invoked_at < returned_at,
        (None, None) => true,
        _ => false,
    }
}

pub open spec fn history_well_formed(history: ConcurrentHistory) -> bool {
    forall|id: CallId| #![trigger history.calls.dom().contains(id)]
        history.calls.dom().contains(id) ==> call_well_formed(history.calls[id])
}

// A witness chooses which pending calls to complete, orders all completed calls,
// records their outcomes, and gives the abstract database state between steps.
pub struct LinearizationWitness {
    pub order: Seq<CallId>,
    pub outcomes: Map<CallId, DatabaseResult>,
    pub states: Seq<AbstractDatabase>,
}

pub open spec fn occurs(order: Seq<CallId>, id: CallId) -> bool {
    exists|i: int| 0 <= i < order.len() && order[i] == id
}

pub open spec fn order_has_no_duplicates(order: Seq<CallId>) -> bool {
    forall|i: int, j: int| #![trigger order[i], order[j]]
        0 <= i < j < order.len() ==> order[i] != order[j]
}

pub open spec fn witness_contains_legal_calls(
    history: ConcurrentHistory,
    witness: LinearizationWitness,
) -> bool {
    &&& order_has_no_duplicates(witness.order)
    &&& forall|i: int| #![trigger witness.order[i]] 0 <= i < witness.order.len() ==> {
        let id = witness.order[i];
        &&& history.calls.dom().contains(id)
        &&& witness.outcomes.dom().contains(id)
        &&& match history.calls[id].result {
            Some(actual_result) => witness.outcomes[id] == actual_result,
            None => true,
        }
    }
    // Every completed operation must appear. A pending call may either be
    // omitted or included with a legal completion, as in the standard definition.
    &&& forall|id: CallId| #![trigger history.calls.dom().contains(id)]
        history.calls.dom().contains(id) && completed(history.calls[id])
            ==> occurs(witness.order, id)
}

// If call A returned before call B was invoked, A must precede B in the
// sequential witness. Overlapping calls may be ordered either way.
pub open spec fn preserves_real_time(
    history: ConcurrentHistory,
    witness: LinearizationWitness,
) -> bool {
    forall|i: int, j: int| #![trigger witness.order[i], witness.order[j]]
        0 <= i < witness.order.len()
        && 0 <= j < witness.order.len()
        ==> match history.calls[witness.order[i]].returned_at {
            Some(returned_at) =>
                returned_at < history.calls[witness.order[j]].invoked_at ==> i < j,
            None => true,
        }
}

pub open spec fn follows_database_semantics(
    history: ConcurrentHistory,
    initial: AbstractDatabase,
    witness: LinearizationWitness,
) -> bool {
    &&& witness.states.len() == witness.order.len() + 1
    &&& witness.states[0] == initial
    &&& forall|i: int| #![trigger witness.order[i], witness.states[i]]
        0 <= i < witness.order.len() ==> {
            let id = witness.order[i];
            database_step(
                witness.states[i],
                history.calls[id].operation,
                witness.outcomes[id],
                witness.states[i + 1],
            )
        }
}

// This is the concurrent linearizability specification. It quantifies over a
// complete overlapping-call history rather than attaching one atomic contract
// to each function declaration.
pub open spec fn linearizable(
    initial: AbstractDatabase,
    history: ConcurrentHistory,
) -> bool {
    &&& history_well_formed(history)
    &&& exists|witness: LinearizationWitness|
        witness_contains_legal_calls(history, witness)
        && preserves_real_time(history, witness)
        && follows_database_semantics(history, initial, witness)
}

}

fn main() {}
