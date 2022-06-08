#include "fc_common_stubs.h"

#include <rtems/score/mrsp.h>
#include <rtems/score/threadqimpl.h>

/*@ ghost
  extern const int g_core;
  extern Scheduler_Control *g_homesched;
  extern Scheduler_Node *g_homenode;
  extern bool prioritiesUpdated;
  extern Thread_Control *g_thread_inherited;
  extern Thread_Control *g_thread_revoked;
  extern Thread_Control *g_new_owner;
  extern Priority_Control g_prio;
*/

/*@
  global invariant core_max: 0 <= g_core < 32;
  logic Thread_Control* MrsP_Owner(MRSP_Control *m) =
    m->Wait_queue.Queue.owner;
  logic Priority_Control MrsP_Ceiling(MRSP_Control *m) =
    m->Ceiling_priority.priority;
  logic Priority_Control MrsP_Localceiling(MRSP_Control *m) =
    m->ceiling_priorities[g_core];
  logic Priority_Control Executing_Priority =
    g_homenode->Wait.Priority.Node.priority;
  predicate MrsPThreadsWaiting(MRSP_Control *m) =
    m->Wait_queue.Queue.heads != NULL;
  predicate PriorityRevoked(Thread_Control *t, Priority_Control p) =
    t == g_thread_revoked && p == g_prio && prioritiesUpdated;
  predicate PriorityInherited(Thread_Control *t, Priority_Control p) =
    t == g_thread_inherited && p == g_prio && prioritiesUpdated;  
*/

//@ assigns \nothing;
RTEMS_INLINE_ROUTINE void _MRSP_Acquire_critical(
  MRSP_Control         *mrsp,
  Thread_queue_Context *queue_context
);

//@ assigns \nothing;
RTEMS_INLINE_ROUTINE void _MRSP_Release(
  MRSP_Control         *mrsp,
  Thread_queue_Context *queue_context
);

/*@
  assigns \nothing;
  ensures \result == MrsP_Owner(mrsp);
*/
RTEMS_INLINE_ROUTINE Thread_Control *_MRSP_Get_owner(
  const MRSP_Control *mrsp
);

/*@
  requires \valid(mrsp);
  assigns mrsp->Wait_queue.Queue.owner;
  ensures MrsP_Owner(mrsp) == owner;
*/
RTEMS_INLINE_ROUTINE void _MRSP_Set_owner(
  MRSP_Control   *mrsp,
  Thread_Control *owner
);

/*@
  requires \valid(the_thread);
  assigns \nothing;
  ensures \result == g_homesched;
*/
RTEMS_INLINE_ROUTINE const Scheduler_Control *_Thread_Scheduler_get_home(
  const Thread_Control *the_thread
);

/*@
  requires \valid(the_thread);
  assigns \nothing;
  ensures \result == g_homenode;
*/
RTEMS_INLINE_ROUTINE Scheduler_Node *_Thread_Scheduler_get_home_node(
  const Thread_Control *the_thread
);

/*@
  requires \valid(mrsp);
  requires \valid(&mrsp->ceiling_priorities[0 .. g_core-1]);
  requires \valid(scheduler);
  requires scheduler == g_homesched;
  assigns \nothing;
  ensures \result == MrsP_Localceiling(mrsp);
*/
RTEMS_INLINE_ROUTINE Priority_Control _MRSP_Get_priority(
  const MRSP_Control      *mrsp,
  const Scheduler_Control *scheduler
);

/*@
  requires \valid(node);
  ensures node->priority == priority;
  assigns node->priority;
*/
RTEMS_INLINE_ROUTINE void _Priority_Node_initialize(
  Priority_Node    *node,
  Priority_Control  priority
);

/*@
  requires \valid(the_thread) && \valid(priority_node) && \valid(g_homenode);
  assigns g_homenode->Wait.Priority.Node.priority, g_thread_inherited, g_prio;
  ensures g_thread_inherited == the_thread && g_prio == priority_node->priority;
  ensures Executing_Priority == priority_node->priority;
  ensures Executing_Priority <= \old(Executing_Priority);
*/
void _Thread_Priority_add(
  Thread_Control       *the_thread,
  Priority_Node        *priority_node,
  Thread_queue_Context *queue_context
);

/*@
  assigns prioritiesUpdated;
  ensures prioritiesUpdated;
*/
void _Thread_Priority_and_sticky_update(
  Thread_Control *the_thread,
  int             sticky_level_change
);

/*@
  requires \valid(mrsp) && \valid(thread) && \valid(ceiling_priority);
  assigns mrsp->Ceiling_priority.priority;
  ensures MrsP_Ceiling(mrsp) == ceiling_priority->priority;
*/
  RTEMS_INLINE_ROUTINE void _MRSP_Replace_priority(
  MRSP_Control   *mrsp,
  Thread_Control *thread,
  Priority_Node  *ceiling_priority
);

/*@
  requires \valid(thread) && \valid(priority_node);
  assigns g_thread_revoked, g_prio;
  ensures g_thread_revoked == thread && g_prio == priority_node->priority;
  ensures Executing_Priority >= \old(Executing_Priority);
*/
RTEMS_INLINE_ROUTINE void _MRSP_Remove_priority(
  Thread_Control       *thread,
  Priority_Node        *priority_node,
  Thread_queue_Context *queue_context
);

/*@
  requires \valid(queue);
  requires queue->owner == NULL;
  assigns queue->owner, prioritiesUpdated;
  ensures queue->owner == g_new_owner;
  ensures prioritiesUpdated;
*/
void _Thread_queue_Surrender_sticky(
  Thread_queue_Queue            *queue,
  Thread_queue_Heads            *heads,
  Thread_Control                *previous_owner,
  Thread_queue_Context          *queue_context,
  const Thread_queue_Operations *operations
);

/*@
  requires \valid(queue) && \valid(the_thread);
  assigns queue->owner, prioritiesUpdated;
  ensures queue->owner == the_thread;
  ensures prioritiesUpdated;
  ensures \result == STATUS_SUCCESSFUL;
*/
Status_Control _Thread_queue_Enqueue_sticky(
  Thread_queue_Queue            *queue,
  const Thread_queue_Operations *operations,
  Thread_Control                *the_thread,
  Thread_queue_Context          *queue_context
);

/*@
  requires \valid(aggregation);
  assigns \nothing;
  ensures \result == aggregation->Node.priority;
*/
RTEMS_INLINE_ROUTINE Priority_Control _Priority_Get_priority(
  const Priority_Aggregation *aggregation
);

//@ assigns \nothing;
RTEMS_INLINE_ROUTINE void _Thread_queue_Context_set_deadlock_callout(
  Thread_queue_Context          *queue_context,
  Thread_queue_Deadlock_callout  deadlock_callout
);

// bypass inline assembler
#define _ISR_lock_ISR_enable(_context) (void) _context;