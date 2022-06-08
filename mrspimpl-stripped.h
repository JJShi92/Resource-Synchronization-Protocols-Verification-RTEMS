/* ... mrspimpl.h ... */
/*@ ghost
  Scheduler_Control *g_homesched;
  Scheduler_Node *g_homenode;
  Thread_Control *g_thread_revoked, *g_thread_inherited, *g_new_owner;
  const int g_core;
  bool prioritiesUpdated = false;
  Priority_Control g_prio;
*/

/*@
  requires \valid(mrsp) && \valid(thread) && \valid(priority_node) && \valid(g_homesched) && \valid(g_homenode);
  requires \valid_read(&mrsp->ceiling_priorities[0 .. g_core-1]);
  requires \separated(mrsp, thread, g_homenode) && \separated(thread, priority_node, g_homenode);
  behavior raise_success:
    assumes MrsP_Localceiling(mrsp) <= Executing_Priority;
    ensures Executing_Priority == MrsP_Localceiling(mrsp);
    ensures Executing_Priority <= \old(Executing_Priority);
    ensures priority_node->priority == MrsP_Localceiling(mrsp);
    ensures g_thread_inherited == thread && g_prio == MrsP_Localceiling(mrsp);
    ensures \result == STATUS_SUCCESSFUL;
    ensures \valid(mrsp) && \valid(thread) && \valid(priority_node);
    assigns priority_node->priority, g_homenode->Wait.Priority.Node.priority, g_thread_inherited, g_prio;
  behavior raise_fail:
    assumes MrsP_Localceiling(mrsp) > Executing_Priority;
    ensures \result == STATUS_MUTEX_CEILING_VIOLATED;
    ensures MrsP_Owner(mrsp) == \old(MrsP_Owner(mrsp));
  complete behaviors;
  disjoint behaviors;
*/
RTEMS_INLINE_ROUTINE Status_Control _MRSP_Raise_priority(
  MRSP_Control         *mrsp,
  Thread_Control       *thread,
  Priority_Node        *priority_node,
  Thread_queue_Context *queue_context
) { /* ... */ }

/*@
  requires \valid(mrsp) && \valid(executing) && \valid(g_homesched) && \valid(g_homenode);
  requires \valid_read(&mrsp->ceiling_priorities[0 .. g_core-1]);
  requires \separated(mrsp, executing, g_homenode);
  behavior claim_success:
    assumes MrsP_Localceiling(mrsp) <= Executing_Priority;
    ensures Executing_Priority == MrsP_Localceiling(mrsp);
    ensures Executing_Priority <= \old(Executing_Priority);
    ensures MrsP_Owner(mrsp) == executing;
    ensures MrsP_Ceiling(mrsp) == MrsP_Localceiling(mrsp);
    ensures PriorityInherited(executing, MrsP_Ceiling(mrsp));
    ensures \result == STATUS_SUCCESSFUL;
  behavior claim_fail:
    assumes MrsP_Localceiling(mrsp) > Executing_Priority;
    ensures MrsP_Owner(mrsp) == \old(MrsP_Owner(mrsp));
    ensures \result == STATUS_MUTEX_CEILING_VIOLATED;
  complete behaviors;
  disjoint behaviors;
*/
RTEMS_INLINE_ROUTINE Status_Control _MRSP_Claim_ownership(
  MRSP_Control         *mrsp,
  Thread_Control       *executing,
  Thread_queue_Context *queue_context
) { /*...*/ }

/*@
  requires \valid(mrsp) && \valid(executing) && \valid(g_homesched) && \valid(g_homenode);
  requires \valid_read(&mrsp->ceiling_priorities[0 .. g_core-1]);
  requires \separated(mrsp, executing, g_homenode);
  behavior wait_successful:
    assumes MrsP_Localceiling(mrsp) <= Executing_Priority;
    ensures Executing_Priority == MrsP_Localceiling(mrsp);
    ensures Executing_Priority <= \old(Executing_Priority);
    ensures MrsP_Owner(mrsp) == executing;
    ensures MrsP_Ceiling(mrsp) == MrsP_Localceiling(mrsp);
    ensures PriorityInherited(executing, MrsP_Ceiling(mrsp));
    ensures \result == STATUS_SUCCESSFUL;
  behavior wait_fail:
    assumes MrsP_Localceiling(mrsp) > Executing_Priority;
    ensures MrsP_Owner(mrsp) == \old(MrsP_Owner(mrsp));
    ensures \result == STATUS_MUTEX_CEILING_VIOLATED;
  disjoint behaviors;
  complete behaviors;
*/
RTEMS_INLINE_ROUTINE Status_Control _MRSP_Wait_for_ownership(
  MRSP_Control         *mrsp,
  Thread_Control       *executing,
  Thread_queue_Context *queue_context
) {/*...*/}

/*@
  requires \valid(mrsp) && \valid(executing) && \valid(g_homesched) && \valid(g_homenode) && wait;
  requires \valid_read(&mrsp->ceiling_priorities[0 .. g_core-1]);
  requires \separated(mrsp, executing, g_homenode);
  behavior seize_free:
    assumes MrsP_Owner(mrsp) == NULL && Executing_Priority >= MrsP_Localceiling(mrsp);
    ensures MrsP_Owner(mrsp) == executing;
    ensures Executing_Priority == MrsP_Localceiling(mrsp)
      && Executing_Priority <= \old(Executing_Priority);
    ensures MrsP_Ceiling(mrsp) == MrsP_Localceiling(mrsp);
    ensures PriorityInherited(executing, MrsP_Ceiling(mrsp));
    ensures \result == STATUS_SUCCESSFUL;
  behavior seize_wait:
    assumes MrsP_Owner(mrsp) != NULL
      && MrsP_Owner(mrsp) != executing
      && Executing_Priority >= MrsP_Localceiling(mrsp);
    ensures MrsP_Owner(mrsp) == executing;
    ensures Executing_Priority == MrsP_Localceiling(mrsp)
      && Executing_Priority <= \old(Executing_Priority);
    ensures MrsP_Ceiling(mrsp) == MrsP_Localceiling(mrsp);
    ensures PriorityInherited(executing, MrsP_Ceiling(mrsp));
    ensures \result == STATUS_SUCCESSFUL;
  behavior seize_fail_selfowned:
    assumes MrsP_Owner(mrsp) == executing;
    ensures \result == STATUS_UNAVAILABLE;
  behavior seize_fail_ceiling:
    assumes Executing_Priority < MrsP_Localceiling(mrsp)
      && MrsP_Owner(mrsp) != executing;
    ensures \result == STATUS_MUTEX_CEILING_VIOLATED;
  disjoint behaviors;
*/
RTEMS_INLINE_ROUTINE Status_Control _MRSP_Seize(
  MRSP_Control         *mrsp,
  Thread_Control       *executing,
  bool                  wait,
  Thread_queue_Context *queue_context
) {/*...*/}

/*@
  requires \valid(mrsp) && \valid(&mrsp->Wait_queue.Queue) && \valid(executing) && \valid(g_homenode);
  behavior surrender_no_successor:
    assumes MrsP_Owner(mrsp) == executing;
    assumes ! MrsPThreadsWaiting(mrsp);
    ensures MrsP_Owner(mrsp) == NULL;
    ensures PriorityRevoked(executing, MrsP_Ceiling(mrsp));
    ensures Executing_Priority >= \old(Executing_Priority);
    ensures \result == STATUS_SUCCESSFUL;
  behavior surrender_successor:
    assumes MrsP_Owner(mrsp) == executing;
    assumes MrsPThreadsWaiting(mrsp);
    ensures PriorityRevoked(executing, MrsP_Ceiling(mrsp));
    ensures Executing_Priority >= \old(Executing_Priority);
    ensures MrsP_Owner(mrsp) == g_new_owner;
    ensures \result == STATUS_SUCCESSFUL;
  behavior surrender_fail:
    assumes MrsP_Owner(mrsp) != executing;
    ensures \result == STATUS_NOT_OWNER;
  disjoint behaviors;
  complete behaviors;
*/
RTEMS_INLINE_ROUTINE Status_Control _MRSP_Surrender(
  MRSP_Control         *mrsp,
  Thread_Control       *executing,
  Thread_queue_Context *queue_context
) {/*...*/}
/* ... mrspimpl.h ... */