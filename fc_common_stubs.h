#include <rtems/score/coremutex.h>
#include <rtems/score/basedefs.h>
#include <rtems/score/percpu.h>

//@ assigns \nothing;
RTEMS_INLINE_ROUTINE void _Thread_queue_Context_clear_priority_updates(
  Thread_queue_Context *queue_context
);

//@ assigns \nothing;
RTEMS_INLINE_ROUTINE void _Thread_Wait_acquire_default_critical(
  Thread_Control   *the_thread,
  ISR_lock_Context *lock_context
);

//@ assigns \nothing;
RTEMS_INLINE_ROUTINE void _Thread_Wait_release_default_critical(
  Thread_Control   *the_thread,
  ISR_lock_Context *lock_context
);

//@ assigns \nothing;
RTEMS_INLINE_ROUTINE Per_CPU_Control *_Thread_queue_Dispatch_disable(
  Thread_queue_Context *queue_context
);

//@ assigns \nothing;
RTEMS_INLINE_ROUTINE Per_CPU_Control *_Thread_Dispatch_disable_critical(
  const ISR_lock_Context *lock_context
);

//@ assigns \nothing;
void _Thread_Dispatch_enable( Per_CPU_Control *cpu_self );
