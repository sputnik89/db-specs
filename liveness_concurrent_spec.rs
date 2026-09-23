use vstd::prelude::*;

verus! {


pub type Key = Seq<char>;
pub type CallId = nat;
pub type ThreadId = nat;

pub enum DatabaseOperation {
    Get(Key),
    Put(Key, i32),
    Scan(Key, Key),
    Sort,
}

pub enum OperationPhase {
    Invoked,
    Running,
    Linearized,
    Returned,
}

// One operation observed by the liveness model. Its result and database effect
// belong to the separate linearizability/sequential specification.
pub struct LiveCall {
    pub thread: ThreadId,
    pub operation: DatabaseOperation,
    pub phase: OperationPhase,
}

// The implementation may refine this state with locks, queues, versions,
// retries, nodes, or helping records. Liveness observes only call progress.
pub struct ProgressState {
    pub calls: Map<CallId, LiveCall>,
}

// A mathematical infinite trace: execution(time) is the public progress state
// at logical time `time`. It does not imply infinitely many physical threads.
pub type Execution = spec_fn(nat) -> ProgressState;
pub type InitialPredicate = spec_fn(ProgressState) -> bool;
pub type NextRelation = spec_fn(ProgressState, ProgressState) -> bool;
pub type EnabledPredicate = spec_fn(ProgressState, CallId) -> bool;
pub type ScheduledPredicate = spec_fn(ProgressState, ProgressState, CallId) -> bool;

// The trace starts in an allowed state and every adjacent pair is an allowed
// transition of the concrete concurrent algorithm's abstract model.
pub open spec fn valid_execution(
    execution: Execution,
    initial: InitialPredicate,
    next: NextRelation,
) -> bool {
    &&& initial(execution(0))
    &&& forall|time: nat| #![trigger next(execution(time), execution(time + 1))]
        next(execution(time), execution(time + 1))
}

pub open spec fn phase_rank(phase: OperationPhase) -> nat {
    match phase {
        OperationPhase::Invoked => 0,
        OperationPhase::Running => 1,
        OperationPhase::Linearized => 2,
        OperationPhase::Returned => 3,
    }
}

pub open spec fn is_returned(state: ProgressState, id: CallId) -> bool {
    state.calls.dom().contains(id)
        && state.calls[id].phase == OperationPhase::Returned
}

pub open spec fn is_pending(state: ProgressState, id: CallId) -> bool {
    state.calls.dom().contains(id)
        && state.calls[id].phase != OperationPhase::Returned
}

// A call cannot appear already running, linearized, or returned. Requiring an
// explicit invocation prevents malformed traces from manufacturing progress.
pub open spec fn calls_begin_invoked(execution: Execution) -> bool {
    &&& forall|id: CallId| #![trigger execution(0).calls.dom().contains(id)]
        execution(0).calls.dom().contains(id)
            ==> execution(0).calls[id].phase == OperationPhase::Invoked
    &&& forall|time: nat, id: CallId|
        #![trigger execution(time + 1).calls.dom().contains(id)]
        !execution(time).calls.dom().contains(id)
            && execution(time + 1).calls.dom().contains(id)
        ==> execution(time + 1).calls[id].phase == OperationPhase::Invoked
}

// Once a call id appears, it keeps denoting the same thread and operation and
// its public phase never moves backward. Internal implementation steps may
// stutter for arbitrarily many trace positions between public phases.
pub open spec fn calls_evolve_monotonically(execution: Execution) -> bool {
    forall|time: nat, id: CallId|
        #![trigger execution(time).calls.dom().contains(id)]
        execution(time).calls.dom().contains(id) ==> {
            &&& execution(time + 1).calls.dom().contains(id)
            &&& execution(time + 1).calls[id].thread == execution(time).calls[id].thread
            &&& execution(time + 1).calls[id].operation == execution(time).calls[id].operation
            &&& phase_rank(execution(time).calls[id].phase)
                <= phase_rank(execution(time + 1).calls[id].phase)
        }
}

// Once a response is externally visible, later states cannot retract it.
pub open spec fn returned_calls_are_stable(execution: Execution) -> bool {
    forall|time: nat, id: CallId| #![trigger is_returned(execution(time), id)]
        is_returned(execution(time), id) ==> is_returned(execution(time + 1), id)
}

// The call is enabled at every state from `start` onward.
pub open spec fn continuously_enabled_from(
    execution: Execution,
    enabled: EnabledPredicate,
    id: CallId,
    start: nat,
) -> bool {
    forall|time: nat| #![trigger enabled(execution(time), id)]
        start <= time ==> enabled(execution(time), id)
}

// Weak fairness: a continuously enabled call cannot be ignored forever. This
// is normally an assumption about scheduling or lock acquisition fairness.
pub open spec fn weakly_fair(
    execution: Execution,
    enabled: EnabledPredicate,
    scheduled: ScheduledPredicate,
) -> bool {
    forall|id: CallId, start: nat|
        #![trigger continuously_enabled_from(execution, enabled, id, start)]
        continuously_enabled_from(execution, enabled, id, start)
        ==> exists|time: nat| #![trigger scheduled(execution(time), execution(time + 1), id)]
            start <= time
            && scheduled(execution(time), execution(time + 1), id)
}

// The call becomes enabled again after every point in the infinite trace.
pub open spec fn enabled_infinitely_often(
    execution: Execution,
    enabled: EnabledPredicate,
    id: CallId,
) -> bool {
    forall|start: nat| #![trigger execution(start)] exists|time: nat|
        #![trigger enabled(execution(time), id)]
        start <= time && enabled(execution(time), id)
}

// The call is scheduled again after every point in the infinite trace.
pub open spec fn scheduled_infinitely_often(
    execution: Execution,
    scheduled: ScheduledPredicate,
    id: CallId,
) -> bool {
    forall|start: nat| #![trigger execution(start)] exists|time: nat|
        #![trigger scheduled(execution(time), execution(time + 1), id)]
        start <= time && scheduled(execution(time), execution(time + 1), id)
}

// Strong fairness also covers calls that alternate between enabled and
// disabled forever: infinitely-often enabled implies infinitely-often run.
pub open spec fn strongly_fair(
    execution: Execution,
    enabled: EnabledPredicate,
    scheduled: ScheduledPredicate,
) -> bool {
    forall|id: CallId| #![trigger enabled_infinitely_often(execution, enabled, id)]
        enabled_infinitely_often(execution, enabled, id)
            ==> scheduled_infinitely_often(execution, scheduled, id)
}

// Per-call progress (starvation freedom): every call that is pending at any
// observation point eventually returns.
pub open spec fn every_invoked_call_eventually_returns(
    execution: Execution,
) -> bool {
    forall|id: CallId, start: nat| #![trigger is_pending(execution(start), id)]
        is_pending(execution(start), id)
        ==> exists|finish: nat| #![trigger is_returned(execution(finish), id)]
            start <= finish
            && is_returned(execution(finish), id)
}

// System-wide progress: whenever operations are pending, at least one of the
// operations pending at that time eventually returns. This is weaker than
// per-call starvation freedom because a particular call may still starve.
pub open spec fn system_eventually_completes_some_call(
    execution: Execution,
) -> bool {
    forall|start: nat| #![trigger execution(start)]
        (exists|id: CallId| #![trigger is_pending(execution(start), id)]
            is_pending(execution(start), id))
        ==> exists|finish: nat, id: CallId|
            #![trigger is_returned(execution(finish), id)]
            start <= finish
            && is_pending(execution(start), id)
            && is_returned(execution(finish), id)
}

// These are the structural and environmental conditions under which a
// concrete algorithm would establish one of the progress goals below.
pub open spec fn liveness_assumptions(
    execution: Execution,
    initial: InitialPredicate,
    next: NextRelation,
    enabled: EnabledPredicate,
    scheduled: ScheduledPredicate,
) -> bool {
    &&& valid_execution(execution, initial, next)
    &&& calls_begin_invoked(execution)
    &&& calls_evolve_monotonically(execution)
    &&& returned_calls_are_stable(execution)
    &&& weakly_fair(execution, enabled, scheduled)
}

pub open spec fn starvation_freedom_goal(execution: Execution) -> bool {
    every_invoked_call_eventually_returns(execution)
}

pub open spec fn system_progress_goal(execution: Execution) -> bool {
    system_eventually_completes_some_call(execution)
}

// Principal per-call liveness specification. This is a definition of an
// acceptable concurrent execution, parallel to how `linearizable` defines an
// acceptable concurrent history; it is not itself an implementation proof.
pub open spec fn starvation_free_execution(
    execution: Execution,
    initial: InitialPredicate,
    next: NextRelation,
    enabled: EnabledPredicate,
    scheduled: ScheduledPredicate,
) -> bool {
    &&& liveness_assumptions(execution, initial, next, enabled, scheduled)
    &&& starvation_freedom_goal(execution)
}

// Weaker system-wide liveness specification, useful for lock-free algorithms.
pub open spec fn system_makes_progress(
    execution: Execution,
    initial: InitialPredicate,
    next: NextRelation,
    enabled: EnabledPredicate,
    scheduled: ScheduledPredicate,
) -> bool {
    &&& liveness_assumptions(execution, initial, next, enabled, scheduled)
    &&& system_progress_goal(execution)
}

}

fn main() {}
