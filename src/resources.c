#include "resources.h"

#include <sys/time.h>

double kissat_wall_clock_time (void) {
  struct timeval tv;
  if (gettimeofday (&tv, 0))
    return 0;
  return 1e-6 * tv.tv_usec + tv.tv_sec;
}

#ifndef QUIET

#include "internal.h"
#include "statistics.h"
#include "utilities.h"

#include <inttypes.h>
#include <stdio.h>
#include <string.h>

#ifdef _WIN32

// Windows has no getrusage() or /proc. GetProcessMemoryInfo resolves to
// kernel32's K32GetProcessMemoryInfo, so no psapi.dll import is needed.

#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <psapi.h>

static double kissat_filetime_seconds (FILETIME t) {
  ULARGE_INTEGER ticks;
  ticks.LowPart = t.dwLowDateTime;
  ticks.HighPart = t.dwHighDateTime;
  return 1e-7 * (double) ticks.QuadPart;
}

double kissat_process_time (void) {
  FILETIME created, exited, kernel, user;
  if (!GetProcessTimes (GetCurrentProcess (), &created, &exited, &kernel,
                        &user))
    return 0;
  return kissat_filetime_seconds (user) + kissat_filetime_seconds (kernel);
}

static int kissat_memory_counters (PROCESS_MEMORY_COUNTERS *counters) {
  return GetProcessMemoryInfo (GetCurrentProcess (), counters,
                               sizeof *counters);
}

uint64_t kissat_maximum_resident_set_size (void) {
  PROCESS_MEMORY_COUNTERS counters;
  if (!kissat_memory_counters (&counters))
    return 0;
  return counters.PeakWorkingSetSize;
}

uint64_t kissat_current_resident_set_size (void) {
  PROCESS_MEMORY_COUNTERS counters;
  if (!kissat_memory_counters (&counters))
    return 0;
  return counters.WorkingSetSize;
}

#else

#include <sys/resource.h>
#include <sys/types.h>
#include <unistd.h>

double kissat_process_time (void) {
  struct rusage u;
  double res;
  if (getrusage (RUSAGE_SELF, &u))
    return 0;
  res = u.ru_utime.tv_sec + 1e-6 * u.ru_utime.tv_usec;
  res += u.ru_stime.tv_sec + 1e-6 * u.ru_stime.tv_usec;
  return res;
}

uint64_t kissat_maximum_resident_set_size (void) {
  struct rusage u;
  if (getrusage (RUSAGE_SELF, &u))
    return 0;
  return ((uint64_t) u.ru_maxrss) << 10;
}

#ifdef __APPLE__

#include <mach/task.h>
mach_port_t mach_task_self (void);

uint64_t kissat_current_resident_set_size (void) {
  struct task_basic_info info;
  mach_msg_type_number_t count = TASK_BASIC_INFO_COUNT;
  if (KERN_SUCCESS != task_info (mach_task_self (), TASK_BASIC_INFO,
                                 (task_info_t) &info, &count))
    return 0;
  return info.resident_size;
}

#else

uint64_t kissat_current_resident_set_size (void) {
  char path[48];
  sprintf (path, "/proc/%" PRIu64 "/statm", (uint64_t) getpid ());
  FILE *file = fopen (path, "r");
  if (!file)
    return 0;
  uint64_t dummy, rss;
  int scanned = fscanf (file, "%" PRIu64 " %" PRIu64 "", &dummy, &rss);
  fclose (file);
  return scanned == 2 ? rss * sysconf (_SC_PAGESIZE) : 0;
}

#endif

#endif

void kissat_print_resources (kissat *solver) {
  uint64_t rss = kissat_maximum_resident_set_size ();
  double t = kissat_time (solver);
  printf ("%s"
          "%-" SFW1 "s "
          "%" SFW2 PRIu64 " "
          "%-" SFW3 "s "
          "%" SFW4 ".0f "
          "MB\n",
          solver->prefix, "maximum-resident-set-size:", rss, "bytes",
          rss / (double) (1 << 20));
#ifdef METRICS
  statistics *statistics = &solver->statistics;
  uint64_t max_allocated = statistics->allocated_max + sizeof (kissat);
  printf ("%s"
          "%-" SFW1 "s "
          "%" SFW2 PRIu64 " "
          "%-" SFW3 "s "
          "%" SFW4 ".0f "
          "%%\n",
          solver->prefix, "max-allocated:", max_allocated, "bytes",
          kissat_percent (max_allocated, rss));
#endif
  {
    format buffer;
    memset (&buffer, 0, sizeof buffer);
    printf ("%sprocess-time: %30s %18.2f seconds\n", solver->prefix,
            kissat_format_time (&buffer, t), t);
  }
  fflush (stdout);
}

#endif
