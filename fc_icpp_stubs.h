#include "fc_common_stubs.h"

#include <rtems/score/status.h>

//@ assigns \nothing;
RTEMS_INLINE_ROUTINE void _CORE_mutex_Acquire_critical(
  CORE_mutex_Control   *the_mutex,
  Thread_queue_Context *queue_context
);

//@ assigns \nothing;
RTEMS_INLINE_ROUTINE void _CORE_mutex_Release(
  CORE_mutex_Control   *the_mutex,
  Thread_queue_Context *queue_context
);

/*@
  logic Priority_Control Current_Priority(Thread_Control *t) =
    t->Scheduler.nodes->Wait.Priority.Node.priority;
  logic Priority_Control Base_Priority(Thread_Control *t) =
    t->Real_priority.priority;
  logic Priority_Control Mutex_Priority(CORE_ceiling_mutex_Control *m) =
    m->Priority_ceiling.priority;
  logic Thread_Control* CMutex_Owner(CORE_mutex_Control *m) =
    m->Wait_queue.Queue.owner;
  logic Thread_Control* Mutex_Owner(CORE_ceiling_mutex_Control *m) =
    CMutex_Owner(&(m->Recursive.Mutex));
  logic Thread_queue_Control* Mutex_Queue(CORE_ceiling_mutex_Control *m) =
    &m->Recursive.Mutex.Wait_queue;
  logic unsigned int CNest_Level(CORE_recursive_mutex_Control *m) =
      m->nest_level;  
  logic unsigned int Nest_Level(CORE_ceiling_mutex_Control *m) =
      CNest_Level(&(m->Recursive));
*/

/*@
  assigns \nothing;
  ensures \result == CMutex_Owner(the_mutex);
*/
RTEMS_INLINE_ROUTINE Thread_Control *_CORE_mutex_Get_owner(
  const CORE_mutex_Control *the_mutex
);

/*@
  requires \valid(the_mutex);
  assigns *the_mutex;
  ensures CMutex_Owner(the_mutex) == owner;
*/
RTEMS_INLINE_ROUTINE void _CORE_mutex_Set_owner(
  CORE_mutex_Control *the_mutex,
  Thread_Control     *owner
);

/*@
  assigns \nothing;
  ensures \result == (CMutex_Owner(the_mutex) == the_thread);
*/
RTEMS_INLINE_ROUTINE bool _CORE_mutex_Is_owner(
  const CORE_mutex_Control *the_mutex,
  const Thread_Control     *the_thread
);

//@ assigns \nothing;
RTEMS_INLINE_ROUTINE void _Thread_Resource_count_increment(
  Thread_Control *the_thread
);

//@ assigns \nothing;
RTEMS_INLINE_ROUTINE void _Thread_Resource_count_decrement(
  Thread_Control *the_thread
);

/*@
  assigns \result \from the_thread;
  ensures \result == the_thread->Scheduler.nodes;
*/
RTEMS_INLINE_ROUTINE Scheduler_Node *_Thread_Scheduler_get_home_node(
  const Thread_Control *the_thread
);

/*@
  assigns \nothing;
  ensures \result == aggregation->Node.priority;
*/
RTEMS_INLINE_ROUTINE Priority_Control _Priority_Get_priority(
  const Priority_Aggregation *aggregation
);

/*@ ghost // variables declared in coremuteximpl.h
  extern Thread_Control *g_thread_inherited;
  extern Thread_Control *g_thread_revoked;
  extern Priority_Node *g_prio_node;
  extern bool prioritiesUpdated;
*/

/*@
  predicate PriorityInherited(Thread_Control *t, Priority_Control p) =
    t == g_thread_inherited && p == g_prio_node->priority && prioritiesUpdated;
  predicate PriorityRevoked(Thread_Control *t, Priority_Control p) =
    t == g_thread_revoked && p == g_prio_node->priority && prioritiesUpdated;
  predicate QueueEmpty(Thread_queue_Control *q) =
    q->Queue.heads == NULL;    
*/

/*@
  requires \valid(the_thread) && \valid(priority_node);
  assigns *the_thread, g_thread_inherited, g_prio_node;
  ensures g_thread_inherited == the_thread && g_prio_node == priority_node;
  behavior inherit_higher:
    assumes priority_node->priority < Current_Priority(the_thread);
    ensures Current_Priority(the_thread) == priority_node->priority;
  behavior inherit_lower_or_equal:
    assumes priority_node->priority >= Current_Priority(the_thread);
    ensures Current_Priority(the_thread) == \old(Current_Priority(the_thread));
  disjoint behaviors;
  complete behaviors;
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
void _Thread_Priority_update( Thread_queue_Context *queue_context );

/*@
  requires \valid(the_thread) && \valid(priority_node);
  assigns *the_thread, g_thread_revoked, g_prio_node;
  ensures g_thread_revoked == the_thread && g_prio_node == priority_node;
  ensures Current_Priority(the_thread) >= priority_node->priority;
*/
void _Thread_Priority_remove(
  Thread_Control       *the_thread,
  Priority_Node        *priority_node,
  Thread_queue_Context *queue_context
);

/*@ // not used, since on ICPP-release no thread can be waiting
  assigns \nothing;
  behavior empty:
    assumes QueueEmpty(the_thread_queue);
    ensures \result == NULL;
  behavior waiting:
    assumes ! QueueEmpty(the_thread_queue);
    ensures \valid(\result);
  complete behaviors;
  disjoint behaviors;
*/
RTEMS_INLINE_ROUTINE Thread_Control *_Thread_queue_First_locked(
  Thread_queue_Control          *the_thread_queue,
  const Thread_queue_Operations *operations
);

// not used (see above)
//@ assigns \nothing;
void _Thread_queue_Extract_critical(
  Thread_queue_Queue            *queue,
  const Thread_queue_Operations *operations,
  Thread_Control                *the_thread,
  Thread_queue_Context          *queue_context
);

/*@
  requires \valid(the_mutex);
  assigns the_mutex->nest_level;
  ensures CNest_Level(the_mutex) == \old(CNest_Level(the_mutex)) + 1;
  ensures \result == STATUS_SUCCESSFUL;
*/
RTEMS_INLINE_ROUTINE Status_Control _CORE_recursive_mutex_Seize_nested(
  CORE_recursive_mutex_Control *the_mutex
);
