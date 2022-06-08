//test based on testsuites/sptests/spsem02

#include <rtems.h>
#include <stdio.h>
#include "tmacros.h"

/* configuration information */
#define CONFIGURE_APPLICATION_NEEDS_SIMPLE_CONSOLE_DRIVER
#define CONFIGURE_APPLICATION_NEEDS_CLOCK_DRIVER
#define CONFIGURE_INITIAL_EXTENSIONS RTEMS_TEST_INITIAL_EXTENSION
#define CONFIGURE_RTEMS_INIT_TASKS_TABLE
#define CONFIGURE_MAXIMUM_TASKS 4
#define CONFIGURE_MAXIMUM_SEMAPHORES 2
#define CONFIGURE_INIT
#include <rtems/confdefs.h>

const char rtems_test_name[] = "SPSEMCEIL 1";

rtems_task Task01(rtems_task_argument ignored);
rtems_task Task02(rtems_task_argument ignored);
rtems_task Task03(rtems_task_argument ignored);
rtems_task Init(rtems_task_argument ignored);

static int getprio(void)
{
  rtems_status_code status;
  rtems_task_priority pri;
  // retrieves and stores executing thread's current priority to 'pri'
  status = rtems_task_set_priority(RTEMS_SELF, RTEMS_CURRENT_PRIORITY, &pri);
  directive_failed( status, "rtems_task_set_priority");
  return (int)pri;
}

rtems_id   Task_id[3];
rtems_name Task_name[3];
rtems_id   sem_id[2];
rtems_name sem_name[2];

rtems_task Init(rtems_task_argument ignored)
{
  rtems_status_code status;
  rtems_attribute sem_attr;

  TEST_BEGIN();

  sem_attr = RTEMS_BINARY_SEMAPHORE | RTEMS_PRIORITY | RTEMS_PRIORITY_CEILING;
  sem_name[0] = rtems_build_name( 'S','0',' ',' ');
  status = rtems_semaphore_create(
    sem_name[0],
    1,
    sem_attr,
    20, //used by T3 and T2
    &sem_id[0]
  );
  directive_failed( status, "rtems_semaphore_create of S0");
  printf("init: S0 created with ceiling 20 (used by T3 and T2)\n");

  sem_name[1] = rtems_build_name( 'S','1',' ',' ');
  status = rtems_semaphore_create(
    sem_name[1],
    1,
    sem_attr,
    10, //used by T3 and T1
    &sem_id[1]
  );
  directive_failed( status, "rtems_semaphore_create of S1");
  printf("init: S1 created with ceiling 10 (used by T3 and T1)\n");

  Task_name[0] = rtems_build_name( 'T','1',' ',' ');
  status = rtems_task_create(
    Task_name[0],
    10,
    RTEMS_MINIMUM_STACK_SIZE,
    RTEMS_DEFAULT_MODES,
    RTEMS_DEFAULT_ATTRIBUTES,
    &Task_id[0]
  );
  directive_failed( status, "rtems_task_create of T1");
  printf("init: T1 created with priority 10\n");

  Task_name[1] = rtems_build_name( 'T','2',' ',' ');
  status = rtems_task_create(
    Task_name[1],
    20,
    RTEMS_MINIMUM_STACK_SIZE,
    RTEMS_DEFAULT_MODES,
    RTEMS_DEFAULT_ATTRIBUTES,
    &Task_id[1]
  );
  directive_failed( status , "rtems_task_create of T2\n");
  printf("init: T2 created with priority 20\n");

  Task_name[2] = rtems_build_name( 'T','3',' ',' ');
  status = rtems_task_create(
    Task_name[2],
    30,
    RTEMS_MINIMUM_STACK_SIZE,
    RTEMS_DEFAULT_MODES,
    RTEMS_DEFAULT_ATTRIBUTES,
    &Task_id[2]
  );
  directive_failed( status , "rtems_task_create of T3\n");
  printf("init: T3 created with priority 30\n");

  status = rtems_task_start( Task_id[2], Task03, 0);
  directive_failed( status, "rtems_task_start of T3");

  rtems_task_exit();
}

// Task T3 starts with priority 30
rtems_task Task03(rtems_task_argument ignored)
{
  rtems_status_code status;
  printf("T3: started with priority %d\n", getprio());

  printf("T3: acquiring S0...\n");
  status = rtems_semaphore_obtain( sem_id[0], RTEMS_NO_WAIT, 0 );
  directive_failed( status, "rtems_semaphore_obtain of S0\n");
  printf("T3: acquired S0, priority %d\n", getprio());

  printf("T3: acquiring S1...\n");
  status = rtems_semaphore_obtain( sem_id[1], RTEMS_NO_WAIT, 0 );
  directive_failed( status, "rtems_semaphore_obtain of S1\n");
  printf("T3: acquired S1, priority %d\n", getprio());

  printf("T3: releasing S0 and S1...\n");
  status = rtems_semaphore_release( sem_id[0] );
  directive_failed( status, "rtems_semaphore_release of S0\n");
  status = rtems_semaphore_release( sem_id[1] );
  directive_failed( status, "rtems_semaphore_release of S1\n");

  printf("T3: running at priority %d\n\n", getprio());
  
  printf("T3: acquiring S1...\n");
  status = rtems_semaphore_obtain( sem_id[1], RTEMS_NO_WAIT, 0 );
  directive_failed( status, "rtems_semaphore_obtain of S1\n");
  printf("T3: acquired S1, priority %d\n", getprio());

  printf("T3: acquiring S0...\n");
  status = rtems_semaphore_obtain( sem_id[0], RTEMS_NO_WAIT, 0 );
  directive_failed( status, "rtems_semaphore_obtain of S0\n");
  printf("T3: acquired S0, priority %d\n", getprio());

  printf("T3: releasing S0 and S1...\n");
  status = rtems_semaphore_release( sem_id[0] );
  directive_failed( status, "rtems_semaphore_release of S0\n");
  status = rtems_semaphore_release( sem_id[1] );
  directive_failed( status, "rtems_semaphore_release of S1\n");

  printf("T3: running at priority %d\n", getprio());

  // Start T1 with priority 10 which will preempt us.
  status = rtems_task_start( Task_id[0], Task01, 0);
  directive_failed( status, "rtems_task_start of T1\n");
  
  printf("T3: exiting...\n");

  TEST_END();
  rtems_test_exit(0);
}

// Task T1 starts with priority 10
rtems_task Task01(rtems_task_argument ignored)
{
  rtems_status_code status;
  printf("T1: started with priority %d\n", getprio());

  printf("T1: illegitimately acquiring S0...\n");
  status = rtems_semaphore_obtain( sem_id[0], RTEMS_NO_WAIT, 0 );
  directive_failed( status, "rtems_semaphore_obtain of S0\n");
  printf("T1: acquired S0, priority %d\n", getprio());

  printf("T1: exiting...\n");
  rtems_task_exit();
}

