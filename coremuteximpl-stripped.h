/* ... coremuteximpl.h ... */
/*@ ghost
    Thread_Control *g_thread_revoked = NULL, *g_tread_inherited = NULL;
    Priority_Node *g_prio_node = NULL;
    bool prioritiesUpdated = false;
*/

/*@
  requires \valid(the_mutex) && \valid(owner);
  requires \separated(the_mutex, owner);
  behavior set_owner_ceiling_violation:
    assumes Base_Priority(owner) < Mutex_Priority(the_mutex);
    ensures \result == STATUS_MUTEX_CEILING_VIOLATED;
  behavior set_owner_successful:
    assumes Base_Priority(owner) >= Mutex_Priority(the_mutex);
    assigns *owner, *the_mutex, prioritiesUpdated, g_thread_inherited, g_prio_node;
    ensures Current_Priority(owner) <= Mutex_Priority(the_mutex);
    ensures PriorityInherited(owner, Mutex_Priority(the_mutex));
    ensures Mutex_Owner(the_mutex) == owner;
    ensures \result == STATUS_SUCCESSFUL;
  disjoint behaviors;
  complete behaviors;
*/
RTEMS_INLINE_ROUTINE Status_Control _CORE_ceiling_mutex_Set_owner(
  CORE_ceiling_mutex_Control *the_mutex,
  Thread_Control             *owner,
  Thread_queue_Context       *queue_context
) {/*...*/}

/*@
  requires \valid(the_mutex) && \valid(executing);
  requires \separated(the_mutex, executing);
  requires Mutex_Owner(the_mutex) == NULL || Mutex_Owner(the_mutex) == executing;
  behavior seize_ceiling_violation:
    assumes Mutex_Owner(the_mutex) == NULL &&
      Base_Priority(executing) < Mutex_Priority(the_mutex);
    ensures \result == STATUS_MUTEX_CEILING_VIOLATED;
  behavior seize_successful:
    assumes Mutex_Owner(the_mutex) == NULL &&
      Base_Priority(executing) >= Mutex_Priority(the_mutex);
    ensures PriorityInherited(executing, Mutex_Priority(the_mutex));
    ensures Current_Priority(executing) <= Mutex_Priority(the_mutex);
    ensures Mutex_Owner(the_mutex) == executing;
    ensures \result == STATUS_SUCCESSFUL;
  behavior seize_nested:
    assumes Mutex_Owner(the_mutex) == executing;
    assumes nested == _CORE_recursive_mutex_Seize_nested;
    assigns the_mutex->Recursive.nest_level;
    ensures Nest_Level(the_mutex) == \old(Nest_Level(the_mutex)) + 1;
    ensures \result == STATUS_SUCCESSFUL;
  disjoint behaviors;
*/
RTEMS_INLINE_ROUTINE Status_Control _CORE_ceiling_mutex_Seize(
  CORE_ceiling_mutex_Control    *the_mutex,
  Thread_Control                *executing,
  bool                           wait,
  Status_Control              ( *nested )( CORE_recursive_mutex_Control * ),
  Thread_queue_Context          *queue_context
) { /*...*/
    //@ calls _CORE_recursive_mutex_Seize_nested;
    status = ( *nested )( &the_mutex->Recursive );
    /*...*/
}

/*@
  requires \valid(the_mutex) && \valid(executing);
  requires \separated(the_mutex, executing);
  requires Current_Priority(executing) <= Mutex_Priority(the_mutex);
  requires QueueEmpty( Mutex_Queue(the_mutex) );
  behavior surrender_unused_fail:
    assumes Mutex_Owner(the_mutex) != executing;
    ensures \result == STATUS_NOT_OWNER;
  behavior surrender_nested_successful:
    assumes Mutex_Owner(the_mutex) == executing && Nest_Level(the_mutex) > 0;
    assigns *the_mutex;
    ensures Nest_Level(the_mutex) == \old(Nest_Level(the_mutex)) - 1;
    ensures \result == STATUS_SUCCESSFUL;
  behavior surrender_successful:
    assumes Mutex_Owner(the_mutex) == executing && Nest_Level(the_mutex) <= 0;
    ensures PriorityRevoked(executing, Mutex_Priority(the_mutex));
    ensures Current_Priority(executing) >= Current_Priority(\old(executing));
    ensures \result == STATUS_SUCCESSFUL;
  disjoint behaviors;
*/
RTEMS_INLINE_ROUTINE Status_Control _CORE_ceiling_mutex_Surrender(
  CORE_ceiling_mutex_Control *the_mutex,
  Thread_Control             *executing,
  Thread_queue_Context       *queue_context
) {/*...*/}
/* ... coremuteximpl.h ... */