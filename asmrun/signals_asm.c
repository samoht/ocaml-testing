/***********************************************************************/
/*                                                                     */
/*                                OCaml                                */
/*                                                                     */
/*            Xavier Leroy, projet Gallium, INRIA Rocquencourt         */
/*                                                                     */
/*  Copyright 2007 Institut National de Recherche en Informatique et   */
/*  en Automatique.  All rights reserved.  This file is distributed    */
/*  under the terms of the GNU Library General Public License, with    */
/*  the special exception on linking described in file ../LICENSE.     */
/*                                                                     */
/***********************************************************************/

/* $Id$ */

/* Signal handling, code specific to the native-code compiler */

#if defined(TARGET_amd64) && defined (SYS_linux)
#define _GNU_SOURCE
#endif
#include <signal.h>
#include <stdio.h>
#include "fail.h"
#include "memory.h"
#include "osdeps.h"
#include "signals.h"
#include "signals_machdep.h"
#include "signals_osdep.h"
#include "stack.h"

#ifdef HAS_STACK_OVERFLOW_DETECTION
#include <sys/time.h>
#include <sys/resource.h>
#endif

#ifndef NSIG
#define NSIG 64
#endif

typedef void (*signal_handler)(int signo);

#ifdef _WIN32
extern signal_handler caml_win32_signal(int sig, signal_handler action);
#define signal(sig,act) caml_win32_signal(sig,act)
extern void caml_win32_overflow_detection();
#endif

extern char * caml_code_area_start, * caml_code_area_end;

#define Is_in_code_area(pc) \
 ( ((char *)(pc) >= caml_code_area_start && \
    (char *)(pc) <= caml_code_area_end)     \
   || (Classify_addr(pc) & In_code_area) )

/* This routine is the common entry point for garbage collection
   and signal handling.  It can trigger a callback to Caml code.
   With system threads, this callback can cause a context switch.
   Hence [caml_garbage_collection] must not be called from regular C code
   (e.g. the [caml_alloc] function) because the context of the call
   (e.g. [intern_val]) may not allow context switching.
   Only generated assembly code can call [caml_garbage_collection],
   via the caml_call_gc assembly stubs.  */

void caml_garbage_collection(void)
{
  caml_young_limit = caml_young_start;
  if (caml_young_ptr < caml_young_start || caml_force_major_slice) {
    caml_minor_collection();
  }
  caml_process_pending_signals();
}

DECLARE_SIGNAL_HANDLER(handle_signal)
{
#if !defined(POSIX_SIGNALS) && !defined(BSD_SIGNALS)
  signal(sig, handle_signal);
#endif
  if (sig < 0 || sig >= NSIG) return;
  if (caml_try_leave_blocking_section_hook ()) {
    caml_execute_signal(sig, 1);
    caml_enter_blocking_section_hook();
  } else {
    caml_record_signal(sig);
  /* Some ports cache [caml_young_limit] in a register.
     Use the signal context to modify that register too, but only if
     we are inside Caml code (not inside C code). */
#if defined(CONTEXT_PC) && defined(CONTEXT_YOUNG_LIMIT)
    if (Is_in_code_area(CONTEXT_PC))
      CONTEXT_YOUNG_LIMIT = (context_reg) caml_young_limit;
#endif
  }
}

int caml_set_signal_action(int signo, int action)
{
  signal_handler oldact;
#ifdef POSIX_SIGNALS
  struct sigaction sigact, oldsigact;
#else
  signal_handler act;
#endif

#ifdef POSIX_SIGNALS
  switch(action) {
  case 0:
    sigact.sa_handler = SIG_DFL;
    sigact.sa_flags = 0;
    break;
  case 1:
    sigact.sa_handler = SIG_IGN;
    sigact.sa_flags = 0;
    break;
  default:
    SET_SIGACT(sigact, handle_signal);
    break;
  }
  sigemptyset(&sigact.sa_mask);
  if (sigaction(signo, &sigact, &oldsigact) == -1) return -1;
  oldact = oldsigact.sa_handler;
#else
  switch(action) {
  case 0:  act = SIG_DFL; break;
  case 1:  act = SIG_IGN; break;
  default: act = handle_signal; break;
  }
  oldact = signal(signo, act);
  if (oldact == SIG_ERR) return -1;
#endif
  if (oldact == (signal_handler) handle_signal)
    return 2;
  else if (oldact == SIG_IGN)
    return 1;
  else
    return 0;
}

/* Machine- and OS-dependent handling of bound check trap */

#if defined(TARGET_power) || (defined(TARGET_sparc) && defined(SYS_solaris))
DECLARE_SIGNAL_HANDLER(trap_handler)
{
#if defined(SYS_solaris)
  if (info->si_code != ILL_ILLTRP) {
    /* Deactivate our exception handler and return. */
    struct sigaction act;
    act.sa_handler = SIG_DFL;
    act.sa_flags = 0;
    sigemptyset(&act.sa_mask);
    sigaction(sig, &act, NULL);
    return;
  }
#endif
#if defined(SYS_rhapsody)
  /* Unblock SIGTRAP */
  { sigset_t mask;
    sigemptyset(&mask);
    sigaddset(&mask, SIGTRAP);
    sigprocmask(SIG_UNBLOCK, &mask, NULL);
  }
#endif
  caml_exception_pointer = (char *) CONTEXT_EXCEPTION_POINTER;
  caml_young_ptr = (char *) CONTEXT_YOUNG_PTR;
#if defined(SYS_rhapsody)
  caml_bottom_of_stack = (char *) CONTEXT_SP;
  caml_last_return_address = (uintnat) CONTEXT_PC;
#endif
  caml_array_bound_error();
}
#endif

/* Machine- and OS-dependent handling of stack overflow */

#ifdef HAS_STACK_OVERFLOW_DETECTION

static char * system_stack_top;
static char sig_alt_stack[SIGSTKSZ];

DECLARE_SIGNAL_HANDLER(segv_handler)
{
  struct rlimit limit;
  struct sigaction act;
  char * fault_addr;

  /* Sanity checks:
     - faulting address is word-aligned
     - faulting address is within the stack
     - we are in Caml code */
  fault_addr = CONTEXT_FAULTING_ADDRESS;
  if (((uintnat) fault_addr & (sizeof(intnat) - 1)) == 0
      && getrlimit(RLIMIT_STACK, &limit) == 0
      && fault_addr < system_stack_top
      && fault_addr >= system_stack_top - limit.rlim_cur - 0x2000
#ifdef CONTEXT_PC
      && Is_in_code_area(CONTEXT_PC)
#endif
      ) {
    /* Turn this into a Stack_overflow exception */
#if defined(CONTEXT_YOUNG_PTR) && defined(CONTEXT_EXCEPTION_POINTER)
    caml_exception_pointer = (char *) CONTEXT_EXCEPTION_POINTER;
    caml_young_ptr = (char *) CONTEXT_YOUNG_PTR;
#endif
    caml_raise_stack_overflow();
  }
  /* Otherwise, deactivate our exception handler and return,
     causing fatal signal to be generated at point of error. */
  act.sa_handler = SIG_DFL;
  act.sa_flags = 0;
  sigemptyset(&act.sa_mask);
  sigaction(SIGSEGV, &act, NULL);
}

#endif

/* Initialization of signal stuff */

void caml_init_signals(void)
{
  /* Bound-check trap handling */
#if defined(TARGET_sparc) && defined(SYS_solaris)
  { struct sigaction act;
    sigemptyset(&act.sa_mask);
    SET_SIGACT(act, trap_handler);
    act.sa_flags |= SA_NODEFER;
    sigaction(SIGILL, &act, NULL);
  }
#endif

#if defined(TARGET_power)
  { struct sigaction act;
    sigemptyset(&act.sa_mask);
    SET_SIGACT(act, trap_handler);
#if !defined(SYS_rhapsody)
    act.sa_flags |= SA_NODEFER;
#endif
    sigaction(SIGTRAP, &act, NULL);
  }
#endif

  /* Stack overflow handling */
#ifdef HAS_STACK_OVERFLOW_DETECTION
  {
    stack_t stk;
    struct sigaction act;
    stk.ss_sp = sig_alt_stack;
    stk.ss_size = SIGSTKSZ;
    stk.ss_flags = 0;
    SET_SIGACT(act, segv_handler);
    act.sa_flags |= SA_ONSTACK | SA_NODEFER;
    sigemptyset(&act.sa_mask);
    system_stack_top = (char *) &act;
    if (sigaltstack(&stk, NULL) == 0) { sigaction(SIGSEGV, &act, NULL); }
  }
#endif
#if defined(_WIN32) && !defined(_WIN64)
  caml_win32_overflow_detection();
#endif
}
