-------------------------------- MODULE VSR --------------------------------

(*  VIEWSTAMPED REPLICATION TLA+ SPECIFICATION
Based on Viewstamped Replication Revisited
https://pmg.csail.mit.edu/papers/vr-revisited.pdf

Author: Jack Vanlightly

WORK-IN-PROGRESS!!

So far:
- Normal operations
    - Prepare, PrepareOk
    - GetState, NewState
        - Only triggered by receiving Prepare message from higher view
          which involves log truncation.
        - Matching view trigger not yet implemented.
    - Client table not fully implemented. Client table not actually used yet.
- View changes, but not full client table support.
    - Basic safety and liveness
        - Safety: No executed ops are lost.
        - Liveness: View changes eventually complete.
- No recovery
- No reconfiguration
- No explicit failures
    - Messages may never be received, so the unavailability is 
      kind handled anyway. However, with weak fairness of Next, 
      it doesn't fully explore unavailability of the last 
      possible view.
- No optimizations! So it passes the entire log in some messages
  which of course is out-of-the-question in real systems. Another
  specification will implement these optimizations.

Accronyms used:
- SVC = StartViewChange
- DVC = DoViewChange
- SV  = StartView

Current questions:
1) The view change description in the paper seems to conflict
   with itself. What are the conditions for a replica to change 
   its view number? My interpretation:
        a) when the timer expires, the replica sets v to v+1
        b) when receiving a SVC with higher v. Replica sets v to match message.
        c) when receiving a DVC with higher v. Replica sets v to match message.
        d) When receiving a SV with higher v. Replica sets v to match message.
        d) When SVC, DVC or SV of the same view number, replica makes no change.
        e) SVC, DVC or SV of lower view number are ignored.
   However, in the paper it says:
   "When the new primary receives f + 1
    DOVIEWCHANGE messages from different
    replicas (including itself), it sets its view-number
    to that in the messages."
   This doesn't match my rules (a)-(e), but I can't see what rules
   would make this sentence in the paper valid. 

Defects so far:
1) State transfer can cause data loss. 3 view changes, 3 replicas and 3 values
  are the smallest known model required. The issue is caused by two things:
    a) When GetState is sent (due to higher view number), 
       the replica truncates its log to its commit number, there by  
       reducing the number of copies of one or more committed operations 
       from a majority to a minority. Doesn't take into account that 
       the commit number on a follower replica can be stale.
    b) When a replica that has truncated operations due to state
       transfer participates in a view change, it may have the highest
       v' (last normal view) in a DVC message but a smaller log (because it truncated it).
       So it's truncated log can win, and therefore overwrite committed entries.

A fix has not yet been explored, but these could involve not truncating
on GetState, but overwriting on receiving NewState. Other, better
options may exist.

*)

EXTENDS Naturals, FiniteSets, FiniteSetsExt, Sequences, SequencesExt, TLC, TLCExt

\* Model size
CONSTANTS ReplicaCount,
          ClientCount,
          Values,
          StartViewOnTimerLimit

\* Status          
CONSTANTS Normal,
          ViewChange,
          Recovering

\* Message types          
CONSTANTS RequestMsg,
          ReplyMsg,
          PrepareMsg,
          PrepareOkMsg,
          CommitMsg,
          StartViewChangeMsg,
          DoViewChangeMsg,
          StartViewMsg,
          GetStateMsg,
          NewStateMsg,
          RecoveryMsg,
          RecoveryResponseMsg
                              
CONSTANTS Nil

VARIABLES replicas,                 \* set of replicas as integers
          rep_status,               \* function of replica -> status
          rep_log,                  \* function of replica -> log
          rep_view_number,          \* function of replica -> view number
          rep_op_number,            \* function of replica -> op number
          rep_commit_number,        \* function of replica -> commit number
          rep_peer_op_number,       \* function of replica -> peer op number
          rep_client_table,         \* function of replica -> client table
          rep_last_normal_view,     \* function of replica -> last normal view
          rep_svc_recv,             \* function of replica -> set of SVC msgs received
          rep_dvc_recv,             \* function of replica -> set of DVC msgs received
          rep_sent_dvc,             \* function of replica -> TRUE/FALSE whether DVC was sent
          rep_sent_sv,              \* function of replica -> TRUE/FALSE whether SV was sent
          clients,
          messages,                 \* messages as a function of message -> pending deliveries
          aux_svc,                  \* used to track number of times a timer-based SVC is sent
          aux_client_acked          \* used to track which operations have been acknowledged

rep_state_vars == << rep_status, rep_log, rep_view_number, rep_op_number, rep_peer_op_number,
                     rep_commit_number, rep_client_table, rep_last_normal_view >>
rep_vc_vars == << rep_svc_recv, rep_dvc_recv, rep_sent_dvc, rep_sent_sv >>
client_vars    == << >>
aux_vars       == << aux_svc, aux_client_acked >>             
vars           == << rep_state_vars, rep_vc_vars, client_vars, aux_vars, 
                     replicas, clients, messages >> 
          
\*****************************************
\* Message passing
\*****************************************

LogEntryType ==
    [view_number: Nat,
     operation: Values,
     client_id: Nat,
     request_number: Nat]
     
PrepareMsgType ==
    [type: PrepareMsg,
     view_number: Nat,
     message: LogEntryType,
     op_number: Nat,
     commit_number: Nat,
     dest: Nat,
     source: Nat]
     
PrepareOkMsgType ==
    [type: PrepareOkMsg,
     view_number: Nat,
     op_number: Nat,
     dest: Nat,
     source: Nat]     
     
CommitMsgType ==
    [type: CommitMsg,
     view_number: Nat,
     commit_number: Nat,
     dest: Nat,
     source: Nat]
     
StartViewChangeMsgType ==
    [type: StartViewChangeMsg,
     view_number: Nat,
     dest: Nat,
     source: Nat]
     
DoViewChangeMsgType ==
    [type: DoViewChangeMsg,
     view_number: Nat,
     log: [Nat -> LogEntryType],
     last_normal_vn: Nat,
     op_number: Nat,
     commit_number: Nat,
     dest: Nat,
     source: Nat]
     
StartViewMsgType ==
    [type: StartViewMsg,
     view_number: Nat,
     log: [Nat -> LogEntryType],
     op_number: Nat,
     commit_number: Nat,
     dest: Nat,
     source: Nat]

\* Send the message whether it already exists or not.
SendFunc(m, msgs) ==
    IF m \in DOMAIN msgs
    THEN [msgs EXCEPT ![m] = @ + 1]
    ELSE msgs @@ (m :> 1)

BroadcastFunc(msg, source, msgs) ==
    LET bcast_msgs == { [msg EXCEPT !.dest = r] 
                    : r \in replicas \ {source} }
        new_msgs   == bcast_msgs \ DOMAIN msgs
    IN [m \in DOMAIN msgs |->
            IF m \in bcast_msgs
            THEN msgs[m] + 1
            ELSE msgs[m]] @@ [r \in new_msgs |-> 1]    

\* Remove a message from the bag of messages. Used when a server is done
\* processing a message.
DiscardFunc(m, msgs) ==
    [msgs EXCEPT ![m] = @ - 1]

Send(m) ==
    messages' = SendFunc(m, messages)

SendOnce(m) ==
    /\ m \notin DOMAIN messages
    /\ messages' = SendFunc(m, messages)

Discard(d) ==
    messages' = DiscardFunc(d, messages)
    
Broadcast(msg, source) ==
    messages' = BroadcastFunc(msg, source, messages) 

DiscardAndBroadcast(d, msg, source) ==
    /\ d \in DOMAIN messages
    /\ messages[d] > 0 \* message must exist
    /\ messages' = BroadcastFunc(msg, 
                     source,
                     DiscardFunc(d, messages))
    
DiscardAndSend(d, m) ==
    /\ d \in DOMAIN messages
    /\ messages[d] > 0 \* message must exist
    /\ messages' = SendFunc(m, DiscardFunc(d, messages))

ReceivableMsg(m, type, r) ==
    /\ m.type = type
    /\ m.dest = r
    /\ messages[m] > 0

\*****************************************
\* Helpers
\*****************************************

View(r) ==
    rep_view_number[r]

\* v=1, rc=3 => p=1
\* v=2, rc=3 => p=2
\* v=3, rc=3 => p=3
Primary(v) ==
    1 + ((v-1) % ReplicaCount)
    
IsPrimary(r) ==
    Primary(View(r)) = r

NewSVCMessage(r, view_number) ==
    [type        |-> StartViewChangeMsg,
     view_number |-> view_number,
     dest        |-> Nil, \* replaced in broadcast
     source      |-> r]

ResetRecvMsgs(r) ==
    /\ rep_svc_recv' = [rep_svc_recv EXCEPT ![r] = {}]
    /\ rep_dvc_recv' = [rep_dvc_recv EXCEPT ![r] = {}]

ResetSentVars(r) ==
    /\ rep_sent_dvc' = [rep_sent_dvc EXCEPT ![r] = FALSE]
    /\ rep_sent_sv' = [rep_sent_sv EXCEPT ![r] = FALSE]
    
MinVal(a, b) ==
    IF a <= b THEN a ELSE b    
    
\*****************************************
\* Actions
\*****************************************

\*****************************************
\* Init
\* Starts off with an established cluster with no data

EmptyClientTableRow ==
    [request_number |-> 0,
     op_number      |-> 0,
     executed       |-> TRUE]

Init ==
    LET replica_ids == 1..ReplicaCount
        client_ids == 1..ClientCount
    IN 
        /\ replicas = replica_ids
        /\ rep_status = [r \in replica_ids |-> Normal]
        /\ rep_log = [r \in replica_ids |-> <<>>]
        /\ rep_view_number = [r \in replica_ids |-> 1]
        /\ rep_op_number = [r \in replica_ids |-> 0]
        /\ rep_commit_number = [r \in replica_ids |-> 0]
        /\ rep_peer_op_number = [r \in replica_ids |->
                                    [r1 \in replica_ids |-> 0]]
        /\ rep_client_table = [r \in replica_ids |-> 
                                [c \in client_ids |-> EmptyClientTableRow]]
        /\ rep_svc_recv = [r \in replica_ids |-> {}]
        /\ rep_dvc_recv = [r \in replica_ids |-> {}]
        /\ rep_sent_dvc = [r \in replica_ids |-> FALSE]
        /\ rep_sent_sv = [r \in replica_ids |-> FALSE]
        /\ rep_last_normal_view = [r \in replica_ids |-> 0]
        /\ clients = client_ids
        /\ messages = <<>>
        /\ aux_svc = 0
        /\ aux_client_acked = <<>>
        
\*****************************************
\* ReceiveClientRequest
\*
\* The client itself is not modeled, only requests
\* arriving that meet the following criteria:
\* - arrive at a replica in Normal status that believes
\*   it is the primary.
\* - there are no outstanding requests from this client
\* - the request number is one larger than the previous
\*   or 1 if no previous.
\* The replica adds the request to its log and broadcasts
\* a Prepare message to all other replicas.
\*
\* Clients are not modeled in order to reduce the state
\* as this protocol has a very large state space already.

ReceiveClientRequest ==
    \E r \in replicas, c \in clients, v \in Values :
        /\ IsPrimary(r)
        /\ rep_status[r] = Normal
        /\ v \notin DOMAIN aux_client_acked
        /\ rep_client_table[r][c].executed = TRUE \* there isn't a pending request for this client
        /\ LET req_number == rep_client_table[r][c].request_number + 1
               op_number  == Len(rep_log[r]) + 1
               log_entry  == [view_number    |-> View(r),
                              operation      |-> v,
                              client_id      |-> c,
                              request_number |-> req_number]
           IN
                /\ rep_log' = [rep_log EXCEPT ![r] = Append(@, log_entry)]
                /\ rep_op_number' = [rep_op_number EXCEPT ![r] = op_number]
                /\ rep_client_table' = [rep_client_table EXCEPT ![r][c] =
                                            [request_number |-> req_number,
                                             op_number      |-> op_number,
                                             executed       |-> FALSE]]
                /\ Broadcast([type          |-> PrepareMsg,
                              view_number   |-> View(r),
                              message       |-> log_entry,
                              op_number     |-> op_number,
                              commit_number |-> rep_commit_number[r],
                              dest          |-> Nil,
                              source        |-> r], r)
                /\ aux_client_acked' = aux_client_acked @@ (v :> FALSE)
    /\ UNCHANGED << rep_status, rep_view_number, rep_commit_number, rep_last_normal_view, rep_peer_op_number,
                    rep_peer_op_number, rep_vc_vars, client_vars, aux_svc, replicas, clients >>
                    
\*****************************************
\* ReceivePrepareMsg
\*
\* A replica receives this message only when in the
\* normal status and when the view of the message matches
\* its own. A replica will only process Prepare messages
\* in order. Any out-of-order messages can be buffered.
\* The replica responds by sending a PrepareOk message.

ReceivePrepareMsg ==
    \E r \in replicas, m \in DOMAIN messages :
        /\ ReceivableMsg(m, PrepareMsg, r)
        /\ rep_status[r] = Normal
        /\ m.view_number = View(r)
        /\ m.op_number = rep_op_number[r] + 1
        /\ rep_log' = [rep_log EXCEPT ![r] = Append(@, m.message)]
        /\ rep_op_number' = [rep_op_number EXCEPT ![r] = m.op_number]
        /\ rep_commit_number' = [rep_commit_number EXCEPT ![r] = m.commit_number]
        /\ rep_client_table' = [rep_client_table EXCEPT ![r] = 
                                    [c \in DOMAIN rep_client_table[r] |->
                                        IF c = m.message.client_id
                                        THEN [request_number |-> m.message.request_number,
                                              op_number      |-> m.op_number,
                                              executed       |-> m.op_number <= m.commit_number]
                                        ELSE [rep_client_table[r][c] EXCEPT !.executed = 
                                                    rep_client_table[r][c].op_number <= m.commit]]]
        /\ DiscardAndSend(m, [type        |-> PrepareOkMsg,
                              view_number |-> View(r),
                              op_number   |-> m.op_number,
                              dest        |-> m.source,
                              source      |-> r])
        /\ UNCHANGED << rep_status, rep_view_number, rep_last_normal_view, rep_peer_op_number, 
                        rep_vc_vars, client_vars, aux_vars, replicas, clients >>

\*****************************************
\* ReceivePrepareOkMsg
\*
\* The primary receives a PrepareOk message and registers
\* it for counting purposes (to know when it can execute and
\* commit the operation).

ReceivePrepareOkMsg ==
   \E r \in replicas, m \in DOMAIN messages :
        /\ ReceivableMsg(m, PrepareOkMsg, r)
        /\ IsPrimary(r)
        /\ rep_status[r] = Normal
        /\ m.view_number = View(r)
        /\ m.op_number > rep_peer_op_number[r][m.source]
        /\ rep_peer_op_number' = [rep_peer_op_number EXCEPT ![r][m.source] = m.op_number]
        /\ Discard(m)
        /\ UNCHANGED << rep_status, rep_view_number, rep_log, rep_op_number, rep_commit_number, rep_client_table, 
                        rep_last_normal_view, rep_vc_vars, client_vars, aux_vars, replicas, clients >>


\*****************************************
\* ExecuteOp
\*
\* The replica executes the op (which in this spec)
\* is basically a no-op and advances the commit number
\* accordinfgly.

IsCommitted(r, op_number) ==
    Quantify(replicas, 
             LAMBDA peer : rep_peer_op_number[r][peer] >= op_number)
             >= ReplicaCount \div 2

ExecuteOp ==
   \E r \in replicas :
        /\ IsPrimary(r)
        /\ rep_status[r] = Normal
        /\ rep_commit_number[r] < rep_op_number[r]
        /\ IsCommitted(r, rep_commit_number[r] + 1)
        /\ LET op_number == rep_commit_number[r] + 1
               op        == rep_log[r][op_number]
           IN
                /\ rep_commit_number' = [rep_commit_number EXCEPT ![r] = op_number]
                /\ rep_client_table' = [rep_client_table EXCEPT ![r][op.client_id].executed = TRUE]
                /\ aux_client_acked' = [aux_client_acked EXCEPT ![op.operation] = TRUE]
        /\ UNCHANGED << rep_status, rep_view_number, rep_log, rep_op_number, rep_peer_op_number,
                        rep_last_normal_view, rep_vc_vars, client_vars, aux_svc, replicas, clients, messages >>
        

\*****************************************
\* SendGetState
\*
\* A replica receives a Prepare message from
\* a higher view than its own and with a gap
\* between the message operation and the replicas
\* op number. Therefore it needs to perform
\* state transfer to get the missing operations
\* before it can process this Prepare message.
\* It truncates its log to the commit number
\* and sends a GetState message to a peer.

TruncateLogToCommitNumber(r, truncate_to) ==
    IF truncate_to = 0
    THEN <<>>
    ELSE [n \in 1..truncate_to |-> rep_log[r][n]] 

SendGetState ==
    \E r, rDest \in replicas, m \in DOMAIN messages :
        /\ ~IsPrimary(r)
        /\ r # rDest
        /\ ReceivableMsg(m, PrepareMsg, r)
        /\ rep_status[r] = Normal
        /\ m.view_number > View(r)
        /\ m.op_number > rep_op_number[r] + 1
        /\ LET truncate_to == MinVal(rep_commit_number[r], Len(rep_log[r]))
           IN
                /\ rep_log' = [rep_log EXCEPT ![r] = TruncateLogToCommitNumber(r, truncate_to)]
                /\ rep_op_number' = [rep_op_number EXCEPT ![r] = truncate_to]
                /\ rep_view_number' = [rep_view_number EXCEPT ![r] = m.view_number]
                /\ rep_last_normal_view' = [rep_last_normal_view EXCEPT ![r] = m.view_number]
                /\ SendOnce([type        |-> GetStateMsg,
                             view_number |-> m.view_number,
                             op_number   |-> truncate_to,
                             dest        |-> rDest,
                             source      |-> r])
        /\ UNCHANGED << rep_status, rep_peer_op_number, rep_client_table, rep_commit_number,
                        rep_vc_vars, client_vars, aux_vars, replicas, clients >>

\*****************************************
\* ReceiveGetState
\*
\* A replica receives a GetState message with a 
\* matching view and sends its log that is higher
\* than the message op number.
\* It ignores GetState messages with an op number that is
\* higher or equal to its own.
ReceiveGetState ==
    \E r \in replicas, m \in DOMAIN messages :
        /\ ReceivableMsg(m, GetStateMsg, r)
        /\ View(r) = m.view_number
        /\ rep_status[r] = Normal
        /\ rep_op_number[r] > m.op_number
        /\ DiscardAndSend(m, 
                [type          |-> NewStateMsg,
                 view_number   |-> View(r),
                 log           |-> [on \in m.op_number+1..rep_op_number[r] 
                                               |-> rep_log[r][on]],
                 first_op      |-> m.op_number + 1,
                 op_number     |-> rep_op_number[r],
                 commit_number |-> rep_commit_number[r],
                 dest          |-> m.source,
                 source        |-> r])
        /\ UNCHANGED << rep_state_vars, rep_vc_vars, client_vars, 
                        aux_vars, replicas, clients >>

\*****************************************
\* ReceiveNewState
\*
\* A replica receives a NewState message with
\* a matching view while in the normal status.
\* It appends the log entries to its log.                      
ReceiveNewState ==
    \E r \in replicas, m \in DOMAIN messages :
        /\ ReceivableMsg(m, NewStateMsg, r)
        /\ View(r) = m.view_number
        /\ rep_status[r] = Normal
        /\ rep_op_number[r] = m.first_op - 1
        /\ rep_log' = [rep_log EXCEPT ![r] = 
                            [on \in 1..m.op_number |->
                                IF on <= rep_op_number[r]
                                THEN rep_log[r][on]
                                ELSE m.log[on]]]
        /\ rep_op_number' = [rep_op_number EXCEPT ![r] = m.op_number]
        /\ rep_client_table' = rep_client_table \* TODO
        /\ Discard(m)
        /\ UNCHANGED << rep_status, rep_view_number, rep_peer_op_number,
                        rep_commit_number, rep_last_normal_view, rep_vc_vars, client_vars, 
                        aux_vars, replicas, clients >>
                              

\*****************************************
\* TimerSendSVC
\* 
\* StartViewChange on a timer. The replica hasn't 
\* heard from the primary. Broadcasts a SVC message to 
\* all other replicas.
\* Resets recorded (received SVCs and DVCs, sent DVCs and SVs).

TimerSendSVC ==
    /\ aux_svc < StartViewOnTimerLimit
    /\ \E r \in replicas :
        /\ ~IsPrimary(r)
        /\ rep_view_number' = [rep_view_number EXCEPT ![r] = View(r) + 1]
        /\ rep_status' = [rep_status EXCEPT ![r] = ViewChange]
        /\ ResetRecvMsgs(r)
        /\ ResetSentVars(r)
        /\ aux_svc' = aux_svc + 1
        /\ Broadcast(NewSVCMessage(r, View(r) + 1), r)
        /\ UNCHANGED << rep_log, rep_op_number, rep_commit_number, rep_client_table, rep_peer_op_number,
                        rep_last_normal_view, client_vars, replicas, clients, aux_client_acked >>
                      
\*****************************************
\* ReceiveHigherSVC (StartViewChange)
\*
\* A replica receives a StartViewChange message
\* with a higher view number than it's own. The
\* replica updates it view to match and broadcasts
\* a StartViewChange of its own.
\* Resets recorded (received SVCs and DVCs, sent DVCs and SVs)
\* but records the SVC received. 

ReceiveHigherSVC ==
    \E m \in DOMAIN messages, r \in replicas :
        /\ ReceivableMsg(m, StartViewChangeMsg, r)
        /\ m.view_number > rep_view_number[r]
        /\ rep_view_number' = [rep_view_number EXCEPT ![r] = m.view_number]
        /\ rep_status' = [rep_status EXCEPT ![r] = ViewChange]
        /\ rep_svc_recv' = [rep_svc_recv EXCEPT ![r] = {m}]
        /\ rep_dvc_recv' = [rep_dvc_recv EXCEPT ![r] = {}]
        /\ ResetSentVars(r)
        /\ DiscardAndBroadcast(m, NewSVCMessage(r, m.view_number), r)
        /\ UNCHANGED << rep_log, rep_op_number, rep_commit_number, rep_client_table, rep_peer_op_number,
                        rep_last_normal_view, client_vars, aux_vars, replicas, clients >>

\*****************************************
\* ReceiveMatchingSVC (StartViewChange)
\*
\* A replica receives a StartViewChange message
\* with a view number that matches it's own. In this
\* action it simply records the message.
\* NOTE: seems obvious that we shouldn't let a replica
\*       in a switch from normal->view-change status
\*       without a view number change, this could cause 
\*       a liveness issue. Not discussed in the paper.
ReceiveMatchingSVC ==
    \E m \in DOMAIN messages, r \in replicas :
        /\ ReceivableMsg(m, StartViewChangeMsg, r)
        /\ m.view_number = View(r)
        \* prevent switching to ViewChange without a view number change (not in paper)
        /\ rep_status[r] = ViewChange 
        /\ rep_svc_recv' = [rep_svc_recv EXCEPT ![r] = @ \union {m}]
        /\ Discard(m)
        /\ UNCHANGED << rep_state_vars, rep_dvc_recv, rep_sent_dvc, rep_sent_sv,
                        client_vars, aux_vars, replicas, clients >>

\*****************************************
\* SendDVC (DoViewChange)
\* The replica has received StartViewChange messages
\* from a minority (f) replicas and therefore sends
\* a DoViewChange to the primary of this view.
\* It includes:
\* - the highest view number that was in a normal status
\* - it's log (this will be replaced by optimizations later on)
\* - the view number, op number and commit number.
\* If the primary is itself, it doesn't send the message, it
\* only registers it for counting.

SendDVC ==
    \E r \in replicas :
        /\ rep_status[r] = ViewChange
        /\ rep_sent_dvc[r] = FALSE
        /\ Cardinality(rep_svc_recv[r]) >= ReplicaCount \div 2
        /\ rep_sent_dvc' = [rep_sent_dvc EXCEPT ![r] = TRUE]
        /\ LET msg == [type           |-> DoViewChangeMsg,
                       view_number    |-> View(r),
                       log            |-> rep_log[r],
                       last_normal_vn |-> rep_last_normal_view[r],
                       op_number      |-> rep_op_number[r],
                       commit_number  |-> rep_commit_number[r],
                       dest           |-> Primary(View(r)),
                       source         |-> r]
           IN \/ /\ Primary(View(r)) = r
                 /\ rep_dvc_recv' = [rep_dvc_recv EXCEPT ![r] = @ \union {msg}]
                 /\ UNCHANGED messages
              \/ /\ Primary(View(r)) # r
                 /\ Send(msg)
                 /\ UNCHANGED rep_dvc_recv
        /\ UNCHANGED << rep_state_vars, rep_svc_recv, rep_sent_sv,
                        client_vars, aux_vars, replicas, clients >>
            
\*****************************************
\* ReceiveHigherDVC (DoViewChange)
\*
\* A replica receives a DoViewChange with a higher view
\* than its own. The replica updates it view to match 
\* and broadcasts a StartViewChange of its own. 
ReceiveHigherDVC ==
    \E m \in DOMAIN messages, r \in replicas :
        /\ ReceivableMsg(m, DoViewChangeMsg, r)
        /\ m.view_number > rep_view_number[r]
        /\ rep_view_number' = [rep_view_number EXCEPT ![r] = m.view_number]
        /\ rep_status' = [rep_status EXCEPT ![r] = ViewChange]
        /\ rep_svc_recv' = [rep_svc_recv EXCEPT ![r] = {}]
        /\ rep_dvc_recv' = [rep_dvc_recv EXCEPT ![r] = {m}]
        /\ ResetSentVars(r)
        /\ DiscardAndBroadcast(m, NewSVCMessage(r, m.view_number), r)
        /\ UNCHANGED << rep_log, rep_op_number, rep_commit_number, rep_client_table, rep_peer_op_number,
                        rep_last_normal_view, aux_vars, client_vars, replicas, clients >>
            
\*****************************************
\* ReceiveMatchingDVC (DoViewChange)
\*
\* A replica receives a DoViewChange that matches its
\* own view. It only registers the message for counting.

ReceiveMatchingDVC ==
    \E m \in DOMAIN messages, r \in replicas :
        /\ ReceivableMsg(m, DoViewChangeMsg, r)
        /\ View(r) = m.view_number
        /\ rep_dvc_recv' = [rep_dvc_recv EXCEPT ![r] = @ \union {m}]
        /\ Discard(m)
        /\ UNCHANGED << rep_state_vars, rep_svc_recv, rep_sent_dvc, rep_sent_sv,
                        client_vars, aux_vars, replicas, clients >>

\*****************************************
\* SendSV (StartView)
\*
\* A replica has received DoViewChange messages from
\* a majority (including itself) and so it assumes
\* leadership by broadcasting a StartView message to
\* all other replicas. It includes:
\* - the log (this will be replaced by optimizations later on)
\* - the op and commit numbers
\* - sets some vars for accounting purposes

HighestLog(r) ==
    LET m == CHOOSE m \in rep_dvc_recv[r] :
                ~\E m1 \in rep_dvc_recv[r] :
                    \/ m1.last_normal_vn > m.last_normal_vn
                    \/ /\ m1.last_normal_vn = m.last_normal_vn
                       /\ m1.op_number > m.op_number
    IN m.log

HighestOpNumber(r) ==
    IF HighestLog(r) = <<>>
    THEN 0
    ELSE Len(HighestLog(r))

HighestCommitNumber(r) ==
    LET m == CHOOSE m \in rep_dvc_recv[r] :
                ~\E m1 \in rep_dvc_recv[r] :
                    \/ m1.commit_number > m.commit_number
    IN m.commit_number
        
SendSV ==
    \E r \in replicas :
        /\ rep_status[r] = ViewChange
        /\ rep_sent_sv[r] = FALSE
        /\ Cardinality(rep_dvc_recv[r]) >= (ReplicaCount \div 2) + 1
        /\ LET new_log == HighestLog(r)
               new_on  == HighestOpNumber(r)
               new_cn  == HighestCommitNumber(r)
           IN
                /\ rep_status' = [rep_status EXCEPT ![r] = Normal]
                /\ rep_view_number' = [rep_view_number EXCEPT ![r] = View(r)]
                /\ rep_log' = [rep_log EXCEPT ![r] = new_log]
                /\ rep_op_number' = [rep_op_number EXCEPT ![r] = new_on]
                /\ rep_peer_op_number' = [rep_peer_op_number EXCEPT ![r] = [r1 \in replicas |-> 0]]
                /\ rep_commit_number' = [rep_commit_number EXCEPT ![r] = new_cn]
                /\ rep_sent_sv' = [rep_sent_sv EXCEPT ![r] = TRUE]
                /\ rep_last_normal_view' = [rep_last_normal_view EXCEPT ![r] = View(r)]
                /\ Broadcast([type          |-> StartViewMsg,
                              view_number   |-> View(r),
                              log           |-> new_log,
                              op_number     |-> new_on,
                              commit_number |-> new_cn,
                              dest          |-> Nil,
                              source        |-> r], r)
        /\ UNCHANGED << rep_client_table, rep_svc_recv, rep_dvc_recv, rep_sent_dvc, 
                        client_vars, aux_vars, replicas, clients >>

\*****************************************
\* ReceiveSV (StartView)
\* A replica receives a StartView message and updates
\* its state accordingly. If the replica has any
\* uncommitted operations in its log, it sends the
\* primary a PrepareOk message with the op number
\* it rceived from the primary.
\* NOTE: There is no restriction about view numbers here,
\*       a replica can switch to an earlier view. Most
\*       likely an omission of the paper.

ReceiveSV ==
    \E m \in DOMAIN messages, r \in replicas :
        /\ ReceivableMsg(m, StartViewMsg, r)
        /\ m.view_number >= View(r)
        /\ rep_status' = [rep_status EXCEPT ![r] = Normal]
        /\ rep_view_number' = [rep_view_number EXCEPT ![r] = m.view_number]
        /\ rep_log' = [rep_log EXCEPT ![r] = m.log]
        /\ rep_op_number' = [rep_op_number EXCEPT ![r] = m.op_number]
        /\ rep_commit_number' = [rep_commit_number EXCEPT ![r] = m.commit_number]
        /\ rep_last_normal_view' = [rep_last_normal_view EXCEPT ![r] = m.view_number]
        /\ ResetRecvMsgs(r)
        /\ ResetSentVars(r)
        /\ IF rep_commit_number[r] < m.op_number
           THEN DiscardAndSend(m, [type        |-> PrepareOkMsg,
                                   view_number |-> m.view_number,
                                   op_number   |-> m.op_number,
                                   dest        |-> Primary(m.view_number),
                                   source      |-> r])
           ELSE Discard(m)
        /\ UNCHANGED << rep_client_table, rep_peer_op_number,  
                        client_vars, aux_vars, replicas, clients >>
                  
       
Next ==
    \* view changes
    \/ TimerSendSVC
    \/ ReceiveHigherSVC
    \/ ReceiveMatchingSVC
    \/ SendDVC
    \/ ReceiveHigherDVC
    \/ ReceiveMatchingDVC
    \/ SendSV
    \/ ReceiveSV
    \* normal operations
    \/ ReceiveClientRequest
    \/ ReceivePrepareMsg
    \/ ReceivePrepareOkMsg
    \/ ExecuteOp
    \/ SendGetState
    \/ ReceiveGetState
    \/ ReceiveNewState
    \* TODO
    \* recovery
    \* TODO
    \* reconfiguration
    \* TODO

\*****************************************
\* Invariants
\*****************************************

NoLogDivergence ==
    \A op_number \in 1..Cardinality(Values) :
        ~\E r1, r2 \in replicas :
            /\ op_number \in DOMAIN rep_log[r1]
            /\ op_number \in DOMAIN rep_log[r2]
            /\ rep_log[r1][op_number] # rep_log[r1][op_number]

ReplicaHasOp(r, v) ==
    \E op_number \in DOMAIN rep_log[r] :
        rep_log[r][op_number].operation = v

AcknowledgedWritesExistOnMajority ==
    \A v \in DOMAIN aux_client_acked :
        \/ v \notin DOMAIN aux_client_acked
        \/ aux_client_acked[v] = FALSE
        \/ /\ aux_client_acked[v] = TRUE
           /\ Quantify(replicas, LAMBDA r : ReplicaHasOp(r, v))
                >= (ReplicaCount \div 2) + 1

AcknowledgedWriteNotLost ==
    \A v \in DOMAIN aux_client_acked :
        \/ v \notin DOMAIN aux_client_acked
        \/ aux_client_acked[v] = FALSE
        \/ /\ aux_client_acked[v] = TRUE
           /\ \E r \in replicas : ReplicaHasOp(r, v)

TestInv == TRUE

\*****************************************
\* Liveness
\*****************************************

AllReplicasMoveToSameView ==
    \A r1, r2 \in replicas :
        /\ rep_view_number[r1] = rep_view_number[r2]
        /\ rep_status[r1] = Normal
        /\ rep_status[r2] = Normal

ViewChangeCompletes ==
    []<>AllReplicasMoveToSameView
    

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)    

=============================================================================
