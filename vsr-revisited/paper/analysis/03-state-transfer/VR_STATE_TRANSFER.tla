-------------------------------- MODULE VR_STATE_TRANSFER --------------------------------

(*  VIEWSTAMPED REPLICATION REVISITED TLA+ SPECIFICATION
Based on Viewstamped Replication Revisited
https://pmg.csail.mit.edu/papers/vr-revisited.pdf

Author: Jack Vanlightly

This specification is part of the VR revisited analysis from my blog.
https://jack-vanlightly.com/analyses/2022/12/20/vr-revisited-an-analysis-with-tlaplus

This specification adds state transfer.

This specification only includes
- Normal operations
- View changes
- State Transfer

and does not include:
- commit messages (which are a liveness optimization not needed at this point in the analysis)
- client table related stuff
- replica recovery
- client recovery
- reconfiguration
- any optimizations

TLA+ beginner quick guide:
1. the "rep_" variables are a function, which programmers know as a map.
   The key is the replica id and the value is the state being stored.
   For example, rep_status might be 1=Normal, 2=ViewChange, 3=Normal.
2. A primed variable, such as rep_status' is describing the value of
   that variable in the next state.
2. When you see EXCEPT, you are seeing one entry in a map being updated.
   For example, rep_status' = [rep_status EXCEPT ![r] = ViewChange] is 
   like rep_status[r] = ViewChange.
   You can read the TLA+ as "rep_status in the next state equals rep_status
   in the current state except that the value associated with key r equals
   ViewChange.

*)

EXTENDS Naturals, FiniteSets, FiniteSetsExt, Sequences, SequencesExt, TLC, TLCExt

\* Model size
CONSTANTS ReplicaCount,             \* the number of replicas in the cluster
          Values,                   \* the values that can be sent by clients
          StartViewOnTimerLimit,    \* state space limiter, number of timer triggered view changes
          NoProgressChangeLimit     \* state space limiter, number of changes to replica liveness

\* Status          
CONSTANTS Normal,
          ViewChange,
          StateTransfer

\* Message types          
CONSTANTS PrepareMsg,
          PrepareOkMsg,
          StartViewChangeMsg,
          DoViewChangeMsg,
          StartViewMsg,
          GetStateMsg,
          NewStateMsg
                              
CONSTANTS Nil,
          AnyDest \* used to signify that a message can be sent to any replica
                  \* can receive a message.

VARIABLES replicas,  \* set of replicas as integers
          messages   \* messages as a function of message -> pending delivery count

\* Replica state stored as functions of [replica -> state].
VARIABLES rep_status,               \* replica status (Normal or ViewChange)
          rep_log,                  \* the replica log
          rep_view_number,          \* the current view number
          rep_op_number,            \* the current op number
          rep_commit_number,        \* the current commit number
          rep_peer_op_number,       \* a map of peer -> op_number used to know when an op can be committed
          rep_last_normal_view,     \* the view when the replica was last in the normal status
          rep_sent_dvc,             \* TRUE/FALSE whether a DVC was sent for the current view number
          rep_sent_sv               \* TRUE/FALSE whether SV was broadcast for the current view number

\* auxilliary variables and variables for controlling liveness
VARIABLES no_progress,              \* used for fine control with weak fairness
          no_progress_ctr,          \* used for fine control with weak fairness
          aux_svc,                  \* used to track number of times a timer-based SVC is sent
          aux_client_acked          \* used to track which operations have been acknowledged

rep_state_vars == << rep_status, rep_log, rep_view_number, rep_op_number, rep_peer_op_number,
                     rep_commit_number, rep_last_normal_view >>
rep_vc_vars == << rep_sent_dvc, rep_sent_sv >>
aux_vars       == << aux_svc, aux_client_acked >>
no_prog_vars   == << no_progress, no_progress_ctr >>             
vars           == << rep_state_vars, rep_vc_vars, aux_vars, 
                     replicas, messages, no_prog_vars >>
                     
view == <<rep_state_vars, rep_vc_vars, no_prog_vars, replicas, messages>>
symmValues == Permutations(Values)
          
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

GetStateMsgType ==     
    [type: GetStateMsg,
     view_number: Nat,
     dest: Nat,
     source: Nat]

NewStateMsgType ==
    [type: NewStateMsg,
     view_number: Nat,
     log: [Nat -> LogEntryType],
     first_op: Nat,
     op_number: Nat,
     commit_number: Nat,
     dest: Nat,
     source: Nat]     
     
\* Send the message whether it already exists or not.
SendFunc(m, msgs, deliver_count) ==
    IF m \in DOMAIN msgs
    THEN [msgs EXCEPT ![m] = @ + 1]
    ELSE msgs @@ (m :> deliver_count)

BroadcastFunc(msg, source, msgs, reps) ==
    LET bcast_msgs == { [msg EXCEPT !.dest = r] 
                    : r \in reps \ {source} }
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
    messages' = SendFunc(m, messages, 1)

SendAsReceived(m) ==
    messages' = SendFunc(m, messages, 0)    

SendOnce(m) ==
    /\ m \notin DOMAIN messages
    /\ messages' = SendFunc(m, messages, 1)

Discard(d) ==
    messages' = DiscardFunc(d, messages)
    
Broadcast(msg, source) ==
    messages' = BroadcastFunc(msg, source, messages, replicas) 

DiscardAndBroadcast(d, msg, source) ==
    /\ d \in DOMAIN messages
    /\ messages[d] > 0 \* message must exist
    /\ messages' = BroadcastFunc(msg, 
                     source,
                     DiscardFunc(d, messages),
                     replicas)
                             
DiscardAndSend(d, m) ==
    /\ d \in DOMAIN messages
    /\ messages[d] > 0 \* message must exist
    /\ messages' = SendFunc(m, DiscardFunc(d, messages), 1)

ReceivableMsg(m, type, r) ==
    /\ m.type = type
    /\ \/ m.dest = r \* the dest is r
       \/ /\ m.dest = AnyDest   \* or the dest is any replica
          /\ m.source # r       \* except the replica that sent it
    /\ messages[m] > 0  \* the message hasn't been delivered yet

\*****************************************
\* Helpers
\*****************************************

View(r) ==
    rep_view_number[r]

LastNormalView(r) ==
    rep_last_normal_view[r]

\* v=1, rc=3 => p=1
\* v=2, rc=3 => p=2
\* v=3, rc=3 => p=3
Primary(v) ==
    1 + ((v-1) % ReplicaCount)
    
IsPrimary(r) ==
    Primary(View(r)) = r

NewSVCMessage(r, dest, view_number) ==
    [type        |-> StartViewChangeMsg,
     view_number |-> view_number,
     dest        |-> dest, 
     source      |-> r]

ResetSentVars(r) ==
    /\ rep_sent_dvc' = [rep_sent_dvc EXCEPT ![r] = FALSE]
    /\ rep_sent_sv' = [rep_sent_sv EXCEPT ![r] = FALSE]
    
MinVal(a, b) ==
    IF a <= b THEN a ELSE b    
    
CanProgress(r) == no_progress[r] = FALSE
   
\*****************************************
\* Actions
\*****************************************

\*****************************************
\* Init
\* Starts off with an established cluster with no data

Init ==
    LET replica_ids == 1..ReplicaCount
    IN 
        /\ replicas = replica_ids
        /\ rep_status = [r \in replica_ids |-> Normal]
        /\ rep_log = [r \in replica_ids |-> <<>>]
        /\ rep_view_number = [r \in replica_ids |-> 1]
        /\ rep_op_number = [r \in replica_ids |-> 0]
        /\ rep_commit_number = [r \in replica_ids |-> 0]
        /\ rep_peer_op_number = [r \in replica_ids |->
                                    [r1 \in replica_ids |-> 0]]
        /\ rep_sent_dvc = [r \in replica_ids |-> FALSE]
        /\ rep_sent_sv = [r \in replica_ids |-> FALSE]
        /\ rep_last_normal_view = [r \in replica_ids |-> 1]
        /\ no_progress = [r \in replica_ids |-> FALSE]
        /\ no_progress_ctr = 0
        /\ messages = <<>>
        /\ aux_svc = 0
        /\ aux_client_acked = <<>>
        
\*****************************************
\* ReceiveClientRequest
\*
\* The client itself is not modeled in this spec, only requests
\* arriving that meet the following criteria:
\* - arrive at a replica in Normal status that believes
\*   it is the primary.
\* - this value has not been sent before (required for invariants).
\* The replica adds the request to its log and broadcasts
\* a Prepare message to all other replicas.

ReceiveClientRequest ==
    \E r \in replicas, v \in Values :
        \* enabling conditions
        /\ CanProgress(r)
        /\ IsPrimary(r)
        /\ rep_status[r] = Normal
        /\ v \notin DOMAIN aux_client_acked
        \* mutations to state
        /\ LET op_number  == Len(rep_log[r]) + 1
               log_entry  == [view_number    |-> View(r),
                              operation      |-> v,
                              client_id      |-> Nil]
           IN
                /\ rep_log' = [rep_log EXCEPT ![r] = Append(@, log_entry)]
                /\ rep_op_number' = [rep_op_number EXCEPT ![r] = op_number]
                /\ Broadcast([type          |-> PrepareMsg,
                              view_number   |-> View(r),
                              message       |-> log_entry,
                              op_number     |-> op_number,
                              commit_number |-> rep_commit_number[r],
                              dest          |-> Nil, \* replaced in broadcast
                              source        |-> r], r)
                /\ aux_client_acked' = aux_client_acked @@ (v :> FALSE)
    /\ UNCHANGED << rep_status, rep_view_number, rep_commit_number, rep_last_normal_view, rep_peer_op_number,
                    rep_peer_op_number, rep_vc_vars, aux_svc, replicas, no_prog_vars >>
                    
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
        \* enabling conditions
        /\ CanProgress(r)
        /\ rep_status[r] = Normal
        /\ ~IsPrimary(r)
        /\ ReceivableMsg(m, PrepareMsg, r)
        /\ m.view_number = View(r)
        /\ m.op_number = rep_op_number[r] + 1
        \* mutations to state
        /\ rep_log' = [rep_log EXCEPT ![r] = Append(@, m.message)]
        /\ rep_op_number' = [rep_op_number EXCEPT ![r] = m.op_number]
        /\ rep_commit_number' = [rep_commit_number EXCEPT ![r] = m.commit_number]
        /\ DiscardAndSend(m, [type        |-> PrepareOkMsg,
                              view_number |-> View(r),
                              op_number   |-> m.op_number,
                              dest        |-> m.source,
                              source      |-> r])
        /\ UNCHANGED << rep_status, rep_view_number, rep_last_normal_view, rep_peer_op_number, 
                        rep_vc_vars, aux_vars, replicas, no_prog_vars >>

\*****************************************
\* ReceivePrepareOkMsg
\*
\* The primary receives a PrepareOk message and registers
\* it for counting purposes (to know when it can execute and
\* commit the operation). 
\* If it has no op number tracked for this peer it accepts any
\* it is given, as this should be a PrepareOk in response
\* to a StartView message. Else it only processes the PrepareOk
\* message if it one greater than the previous for that peer.

ReceivePrepareOkMsg ==
   \E r \in replicas, m \in DOMAIN messages :
        \* enabling conditions
        /\ CanProgress(r)
        /\ IsPrimary(r)
        /\ rep_status[r] = Normal
        /\ ReceivableMsg(m, PrepareOkMsg, r)
        /\ m.view_number = View(r)
        /\ m.op_number > rep_peer_op_number[r][m.source]
        \* mutations to state
        /\ rep_peer_op_number' = [rep_peer_op_number EXCEPT ![r][m.source] = m.op_number]
        /\ Discard(m)
        /\ UNCHANGED << rep_status, rep_view_number, rep_log, rep_op_number, rep_commit_number, 
                        rep_last_normal_view, rep_vc_vars, aux_vars, replicas, no_prog_vars >>


\*****************************************
\* ExecuteOp
\*
\* The replica executes the op (which in this spec)
\* is basically a no-op and advances the commit number
\* accordingly. Executes the ops in order.

\* IsCommitted is implicitly assuming the replica has the op.
IsCommitted(r, op_number) ==
    Quantify(replicas, 
             LAMBDA peer : rep_peer_op_number[r][peer] >= op_number)
             >= ReplicaCount \div 2

ExecuteOp ==
   \E r \in replicas :
        \* enabling conditions
        /\ CanProgress(r)
        /\ IsPrimary(r)
        /\ rep_status[r] = Normal
        /\ rep_commit_number[r] < rep_op_number[r]
        /\ IsCommitted(r, rep_commit_number[r] + 1)
        \* mutations to state
        /\ LET op_number == rep_commit_number[r] + 1
               op        == rep_log[r][op_number]
           IN
                /\ rep_commit_number' = [rep_commit_number EXCEPT ![r] = op_number]
                /\ aux_client_acked' = [aux_client_acked EXCEPT ![op.operation] = TRUE]
        /\ UNCHANGED << rep_status, rep_view_number, rep_log, rep_op_number, rep_peer_op_number,
                        rep_last_normal_view, rep_vc_vars, aux_svc, 
                        replicas, messages, no_prog_vars >>
        

\*****************************************
\* SendGetState
\*
\* A replica receives a Prepare message from a higher 
\* view than its own and with a gap between the message
\* operation and the replicas op number. 
\* Therefore it needs to perform state transfer to get
\* the missing operations before it can process this Prepare 
\* message.
\* The replica sets its view to that of the Prepare message.
\* In version 2 of the spec, the replica sets its op-number to
\* its commit-number, truncates its log to the commit-number
\* and sends a GetState message to a peer. However, this has
\* been shown to be unsafe.
\* This is version 3 and the replica does not change its 
\* op-number or log.
\* The GetState message is sent to AnyDest which
\* is a trick to avoid the need for resends (and
\* thus much longer histories) when a subset of 
\* other replicas are unavailable. With AnyDest, 
\* any functioning replica can non-deterministically
\* receive the message. SendOnce is used to avoid 
\* the need for an extra variable used to disable 
\* the action once the message is sent.

\*TruncateLogToCommitNumber(r, truncate_to) ==
\*    IF truncate_to = 0
\*    THEN <<>>
\*    ELSE [n \in 1..truncate_to |-> rep_log[r][n]] 

SendGetState ==
    \E r \in replicas, m \in DOMAIN messages :
        \* enabling conditions
        /\ CanProgress(r)
        /\ rep_status[r] = Normal
        /\ ~IsPrimary(r)
        /\ ReceivableMsg(m, PrepareMsg, r)
        /\ m.view_number > View(r)
        /\ m.op_number > rep_op_number[r] + 1
        \* mutations to state
        /\ rep_status' = [rep_status EXCEPT ![r] = StateTransfer]
        /\ rep_view_number' = [rep_view_number EXCEPT ![r] = m.view_number]
        /\ rep_last_normal_view' = [rep_last_normal_view EXCEPT ![r] = m.view_number]
        /\ SendOnce([type        |-> GetStateMsg,
                     view_number |-> m.view_number,
                     op_number   |-> rep_commit_number[r],
                     dest        |-> AnyDest,
                     source      |-> r])
        /\ UNCHANGED << rep_log, rep_op_number, rep_peer_op_number, rep_commit_number,
                        rep_vc_vars, aux_vars, replicas, no_prog_vars >>

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
        \* enabling conditions
        /\ CanProgress(r)
        /\ rep_status[r] = Normal
        /\ ReceivableMsg(m, GetStateMsg, r)
        /\ View(r) = m.view_number
        /\ rep_op_number[r] > m.op_number
        \* mutations to state
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
        /\ UNCHANGED << rep_state_vars, rep_vc_vars, aux_vars, replicas, no_prog_vars >>

\*****************************************
\* ReceiveNewState
\*
\* A replica receives a NewState message with
\* a matching view while in the normal status.
\* It appends the log entries to its log.                      
ReceiveNewState ==
    \E r \in replicas, m \in DOMAIN messages :
        \* enabling conditions
        /\ rep_status[r] = StateTransfer
        /\ CanProgress(r)
        /\ ReceivableMsg(m, NewStateMsg, r)
        /\ View(r) = m.view_number
        /\ rep_op_number[r] = m.first_op - 1
        \* mutations to state
        /\ rep_status' = [rep_status EXCEPT ![r] = Normal]
        /\ rep_log' = [rep_log EXCEPT ![r] = 
                            [on \in 1..m.op_number |->
                                IF on < m.first_op
                                THEN rep_log[r][on]
                                ELSE m.log[on]]]
        /\ rep_op_number' = [rep_op_number EXCEPT ![r] = m.op_number]
        /\ rep_commit_number' = [rep_commit_number EXCEPT ![r] = m.commit_number]
        /\ Discard(m)
        /\ UNCHANGED << rep_view_number, rep_peer_op_number,
                        rep_last_normal_view,  rep_vc_vars, no_prog_vars, aux_vars, replicas >>

\*****************************************
\* TimerSendSVC
\* 
\* Sends a new StartViewChange on a timer. The replica hasn't 
\* heard from the primary. Broadcasts an SVC message to 
\* all other replicas. This specification does not model
\* actual timeouts, it simply allows for the timer to expire
\* at any moment.
\* The NEWVIEWCHANGE mode dictates that a timer can trigger
\* a new view change at any time, including if it didn't
\* get a response. This spec just allows the timer to fire
\* at any time.

TimerSendSVC ==
    \* enabling conditions
    /\ aux_svc < StartViewOnTimerLimit
    /\ \E r \in replicas :
        /\ CanProgress(r)
        /\ ~IsPrimary(r)
        \* mutations to state
        /\ rep_view_number' = [rep_view_number EXCEPT ![r] = View(r) + 1]
        /\ rep_status' = [rep_status EXCEPT ![r] = ViewChange]
        /\ ResetSentVars(r)
        /\ aux_svc' = aux_svc + 1
        /\ Broadcast(NewSVCMessage(r, Nil, View(r) + 1), r)
        /\ UNCHANGED << rep_log, rep_op_number, rep_commit_number, rep_peer_op_number,
                        rep_last_normal_view, replicas, aux_client_acked, no_prog_vars >>
                      
\*****************************************
\* ReceiveHigherSVC (StartViewChange)
\*
\* A replica receives a StartViewChange message
\* with a higher view number than it's own. The
\* replica increments its view and broadcasts
\* a StartViewChange of its own.

ReceiveHigherSVC ==
    \E m \in DOMAIN messages, r \in replicas :
        \* enabling conditions
        /\ CanProgress(r)
        /\ ReceivableMsg(m, StartViewChangeMsg, r)
        /\ m.view_number > View(r)
        \* mutations to state
        /\ rep_view_number' = [rep_view_number EXCEPT ![r] = m.view_number]
        /\ rep_status' = [rep_status EXCEPT ![r] = ViewChange]
        /\ ResetSentVars(r)
        /\ DiscardAndBroadcast(m, NewSVCMessage(r, Nil, m.view_number), r)
        /\ UNCHANGED << rep_log, rep_op_number, rep_commit_number, rep_peer_op_number,
                        rep_last_normal_view, aux_vars, replicas, no_prog_vars >>

\*****************************************
\* ReceiveMatchingSVC (StartViewChange)
\*
\* A replica receives a StartViewChange message
\* with a view number that matches it's own. In this
\* action it simply records the message for counting.
ReceiveMatchingSVC ==
    \E m \in DOMAIN messages, r \in replicas :
        \* enabling conditions
        /\ CanProgress(r)
        /\ rep_status[r] = ViewChange
        /\ ReceivableMsg(m, StartViewChangeMsg, r)
        /\ m.view_number = View(r)
        \* mutations to state
        /\ Discard(m)
        /\ UNCHANGED << rep_state_vars, rep_vc_vars,
                        aux_vars, replicas, no_prog_vars >>

\*****************************************
\* SendDVC (DoViewChange)
\*
\* The replica has received StartViewChange messages
\* with matching view numbers from a minority (f) replicas 
\* and therefore sends a DoViewChange to the primary of this view.
\* It includes:
\* - the highest Last Normal View (v' in the paper)
\* - it's entire log
\* - the view number, op number and commit number.

SendDVC ==
    \E r \in replicas :
        \* enabling conditions
        /\ CanProgress(r)
        /\ rep_status[r] = ViewChange
        /\ rep_sent_dvc[r] = FALSE  \* has not already sent the DVC
        /\ Quantify(DOMAIN messages, LAMBDA m : 
                /\ m.type = StartViewChangeMsg
                /\ m.dest = r
                /\ m.view_number = View(r)
                /\ messages[m] = 0) >= ReplicaCount \div 2
        \* mutations to state
        /\ rep_sent_dvc' = [rep_sent_dvc EXCEPT ![r] = TRUE]
        /\ LET msg == [type           |-> DoViewChangeMsg,
                       view_number    |-> View(r),
                       log            |-> rep_log[r],
                       last_normal_vn |-> LastNormalView(r),
                       op_number      |-> rep_op_number[r],
                       commit_number  |-> rep_commit_number[r],
                       dest           |-> Primary(View(r)),
                       source         |-> r]
           IN \/ /\ Primary(View(r)) = r
                 /\ SendAsReceived(msg)
              \/ /\ Primary(View(r)) # r
                 /\ Send(msg)
        /\ UNCHANGED << rep_state_vars, rep_sent_sv,
                        aux_vars, replicas, no_prog_vars >>
            
\*****************************************
\* ReceiveHigherDVC (DoViewChange)
\*
\* A replica receives a DoViewChange with a higher view
\* than its own. The replica increments it view number
\* and broadcasts a StartViewChange of its own.

ReceiveHigherDVC ==
    \E m \in DOMAIN messages, r \in replicas :
        \* enabling conditions
        /\ CanProgress(r)
        /\ ReceivableMsg(m, DoViewChangeMsg, r)
        /\ m.view_number > View(r)
        \* mutations to state
        /\ rep_view_number' = [rep_view_number EXCEPT ![r] = m.view_number]
        /\ rep_status' = [rep_status EXCEPT ![r] = ViewChange]
        /\ ResetSentVars(r)
        /\ DiscardAndBroadcast(m, NewSVCMessage(r, Nil, m.view_number), r)
        /\ UNCHANGED << rep_log, rep_op_number, rep_commit_number, rep_peer_op_number,
                        rep_last_normal_view, aux_vars, replicas, no_prog_vars >>
           
\*****************************************
\* ReceiveMatchingDVC (DoViewChange)
\*
\* A replica receives a DoViewChange that matches its
\* own view. It only registers the message for counting.

ReceiveMatchingDVC ==
    \E m \in DOMAIN messages, r \in replicas :
        \* enabling conditions
        /\ CanProgress(r)
        /\ rep_status[r] = ViewChange
        /\ ReceivableMsg(m, DoViewChangeMsg, r)
        /\ m.view_number = View(r)
        \* mutations to state
        /\ Discard(m)
        /\ UNCHANGED << rep_state_vars, rep_vc_vars,
                        aux_vars, replicas, no_prog_vars >>

\*****************************************
\* SendSV (StartView)
\*
\* A replica has received DoViewChange messages with the same
\* view as its own, from a majority, including itself, and 
\* so it assumes leadership by broadcasting a StartView message to
\* all other replicas. It includes:
\* - the entire log
\* - the op and commit numbers
\* - sets some vars for accounting purposes

ValidDvc(r, m) ==
    /\ m.view_number = View(r)
    /\ m.type = DoViewChangeMsg
    /\ m.dest = r
    /\ messages[m] = 0
    
HighestLog(r) ==
    LET m == CHOOSE m \in DOMAIN messages :
                /\ ValidDvc(r, m)
                /\ ~\E m1 \in DOMAIN messages :
                    /\ ValidDvc(r, m1)
                    /\ \/ m1.last_normal_vn > m.last_normal_vn
                       \/ /\ m1.last_normal_vn = m.last_normal_vn
                          /\ m1.op_number > m.op_number
    IN m.log

HighestOpNumber(r) ==
    IF HighestLog(r) = <<>>
    THEN 0
    ELSE Len(HighestLog(r))

HighestCommitNumber(r) ==
    LET m == CHOOSE m \in DOMAIN messages :
                /\ ValidDvc(r, m)
                /\ ~\E m1 \in DOMAIN messages :
                    /\ ValidDvc(r, m1)
                    /\ m1.commit_number > m.commit_number
    IN m.commit_number
        
SendSV ==
    \E r \in replicas :
        \* enabling conditions
        /\ CanProgress(r)
        /\ rep_status[r] = ViewChange
        /\ rep_sent_sv[r] = FALSE
        /\ Quantify(DOMAIN messages, LAMBDA m : ValidDvc(r, m)) >= (ReplicaCount \div 2) + 1
        \* mutations to state
        /\ LET new_log  == HighestLog(r)
               new_on   == HighestOpNumber(r)
               new_cn   == HighestCommitNumber(r)
           IN
                /\ rep_status' = [rep_status EXCEPT ![r] = Normal]
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
        /\ UNCHANGED << rep_view_number, rep_sent_dvc, 
                        aux_vars, replicas, no_prog_vars >>

\*****************************************
\* ReceiveSV (StartView)
\*
\* A replica receives a StartView message and updates
\* its state accordingly. If the replica has any
\* uncommitted operations in its log, it sends the
\* primary a PrepareOk message with the op number
\* it received from the primary.

ReceiveSV ==
    \E m \in DOMAIN messages, r \in replicas :
        \* enabling conditions
        /\ CanProgress(r)
        /\ ReceivableMsg(m, StartViewMsg, r)
        /\ \/ /\ m.view_number = View(r)
              /\ rep_status[r] = ViewChange
           \/ m.view_number > View(r)
        \* mutations to state
        /\ rep_status' = [rep_status EXCEPT ![r] = Normal]
        /\ rep_view_number' = [rep_view_number EXCEPT ![r] = m.view_number]
        /\ rep_log' = [rep_log EXCEPT ![r] = m.log]
        /\ rep_op_number' = [rep_op_number EXCEPT ![r] = m.op_number]
        /\ rep_commit_number' = [rep_commit_number EXCEPT ![r] = m.commit_number]
        /\ rep_last_normal_view' = [rep_last_normal_view EXCEPT ![r] = m.view_number]
        /\ ResetSentVars(r)
        /\ IF rep_commit_number[r] < m.op_number
           THEN DiscardAndSend(m, [type        |-> PrepareOkMsg,
                                   view_number |-> m.view_number,
                                   op_number   |-> m.op_number,
                                   dest        |-> Primary(m.view_number),
                                   source      |-> r])
           ELSE Discard(m)
        /\ UNCHANGED << rep_peer_op_number, aux_vars, replicas, no_prog_vars >>
                  
\*****************************************
\* NoProgressChange (for better control over liveness)
\*
\* Changes a minority subset of the replicas to stop progress
\* and the remaining to be able to make progress. Used
\* in combination with weak fairness to allow for simpler
\* liveness properties.
NoProgressChange ==
    /\ no_progress_ctr < NoProgressChangeLimit
    /\ \E reps \in SUBSET replicas :
        /\ Cardinality(reps) <= ReplicaCount \div 2
        /\ no_progress' = [r \in replicas |-> 
                            IF r \in reps
                            THEN TRUE ELSE FALSE]
        /\ no_progress_ctr' = no_progress_ctr + 1
    /\ UNCHANGED << rep_state_vars, rep_vc_vars, 
                    aux_vars, replicas, messages >>

\*****************************************
\* Next state formula
\*       
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
    \* state transfer
    \/ SendGetState
    \/ ReceiveGetState
    \/ ReceiveNewState
    \* liveness
    \/ NoProgressChange

\*****************************************
\* Invariants
\*****************************************

\* INV: NoLogDivergence
NoLogDivergence ==
    \A op_number \in 1..Cardinality(Values) :
        ~\E r1, r2 \in replicas :
            /\ op_number \in DOMAIN rep_log[r1]
            /\ op_number \in DOMAIN rep_log[r2]
            /\ op_number <= rep_commit_number[r1]
            /\ op_number <= rep_commit_number[r2]
            /\ rep_log[r1][op_number] # rep_log[r2][op_number]
            
\* INV: AcknowledgedWritesExistOnMajority
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

\* INV: AcknowledgedWriteNotLost
\* Use this instead of AcknowledgedWritesExistOnMajority when
\* testing total loss of a replica (not included in this
\* spec at this time).
AcknowledgedWriteNotLost ==
    \A v \in DOMAIN aux_client_acked :
        \/ v \notin DOMAIN aux_client_acked
        \/ aux_client_acked[v] = FALSE
        \/ /\ aux_client_acked[v] = TRUE
           /\ \E r \in replicas : ReplicaHasOp(r, v)

\* INV: CommitNumberNeverHigherThanOpNumber
\* This specification uses a simple broadcast method of
\* operation replication which does not take into
\* account the replica follower log end operation
\* (unlike Raft which uses the nextIndex and matchIndex
\* variables). This broadcast method means that
\* the commit number should never be higher than the op
\* number on any replica.
CommitNumberNeverHigherThanOpNumber ==
    \A r \in replicas :
        rep_commit_number[r] <= rep_op_number[r]

TestInv == 
    TRUE
        
\*****************************************
\* Liveness
\*****************************************

(* Note on message loss and liveness
This specification is able to model all combinations of message loss
with regard to safety properties. Messages are modeled as a map of 
message -> pending delivery count. A message CAN be delivered when
its pending delivery count is > 0. HOWEVER, TLC (the model checker)
doesn't have to explore a branch in history where the message gets
delivered. A message never received is equivalent to a message lost.
However, this doesn't work so well for liveness because if we allow
all messages to be lost then we fail our liveness check. So we use
weak fairness to make it so a message that can be processed will 
eventually be delivered and processed - but this prevents us from 
making use of the natural message loss built into the spec. 
In order to test liveness well with scenarios where a message might be
lost or delayed, an extra variable, no_progress, is used to "pause" any 
minority of replicas at a time. This allows TLC to explore histories 
where a minority of replicas don't participate in a view change (say
because the messages were lost) while still using weak fairness. *)

\* LIVENESS: ConvergenceToView
\* Verifies that eventually, all functioning replicas can make
\* progress to reach the same view number.

BlockedOnLastViewChange ==
    /\ aux_svc = StartViewOnTimerLimit
    /\ \E r \in replicas :
        /\ no_progress[r] = TRUE
        /\ \E s \in SUBSET replicas :
            /\ Cardinality(s) > ReplicaCount \div 2
            /\ \A r1 \in s : Primary(View(r1)) = r
    

AllReplicasMoveToSameView ==
    \* if we there are no more view changes left and
    \* a majority think that the Primary is a replica
    \* that can't make progress, then don't apply this
    \* liveness property as it can't be fulfilled due to
    \* the state space constraints used.
    IF BlockedOnLastViewChange
    THEN TRUE
    ELSE \A r1, r2 \in replicas :
            IF CanProgress(r1) /\ CanProgress(r2)
            THEN /\ rep_view_number[r1] = rep_view_number[r2]
                 /\ rep_status[r1] = Normal
                 /\ rep_status[r2] = Normal
            ELSE TRUE

ConvergenceToView ==
    []<>AllReplicasMoveToSameView

\* LIVENESS: OpEventuallyAllOrNothing
PausedOrHasOp(r, v) ==
    \/ ~CanProgress(r)
    \/ BlockedOnLastViewChange
    \/ ReplicaHasOp(r, v)

PausedOrHasNoOp(r, v) ==
    \/ ~CanProgress(r)
    \/ BlockedOnLastViewChange
    \/ ~ReplicaHasOp(r, v)

OpEventuallyAllOrNothing ==
    \A v \in Values :
        v \in DOMAIN aux_client_acked ~> 
            (\/ \A r \in replicas : PausedOrHasOp(r, v)
             \/ \A r \in replicas : PausedOrHasNoOp(r, v))
            

\* All actions except changes to no_progress
\* have weak fairness.

WFActions ==
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
    \* state transfer
    \/ SendGetState
    \/ ReceiveGetState
    \/ ReceiveNewState

Liveness ==
    WF_vars(WFActions)

Spec == Init /\ [][Next]_vars
LivenessSpec == Init /\ [][Next]_vars /\ Liveness

=============================================================================
