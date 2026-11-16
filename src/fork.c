// Fork.workers(n): split the checking among n worker processes forked after
// the export is loaded, so they share the loaded store copy-on-write
// instead of each loading its own (tools/fbean-par.sh, fmain's argv[6]).
// A worker returns its index 0..n-1 and runs single-threaded; with no fork
// (n < 2, or more than FORK_MAX) the answer is 4294967295 and this process
// is the only worker. The parent
// never returns: it waits for every worker and exits with their join, the
// sequential verdict -- any reject 1, else any decline, crash or failed
// fork 2, else 0 and "accept".

#include <sys/wait.h>
#ifdef __linux__
#include <sys/prctl.h>
#endif

#define FORK_MAX 256

// A worker keeps only the forking thread: the pool's threads and the IO
// helpers are gone, so it runs the sequential loop, starts its own helpers,
// and wakes on a pipe of its own (a shared one would hand one worker's IO
// completions to another).
static void fork_child_reset(void) {
  pthread_mutex_init(&pool_lock, NULL);
  pthread_cond_init(&pool_wake, NULL);
  pthread_cond_init(&pool_join, NULL);
  pthread_mutex_init(&io_gate, NULL);
  pthread_cond_init(&io_bell, NULL);
  pool_size = 1;
  io_size   = 0;
  close(io_wake_fd[0]);
  close(io_wake_fd[1]);
  if (pipe(io_wake_fd) | fcntl(io_wake_fd[0], F_SETFL, O_NONBLOCK)) {
    err_fail("pipe");
  }
  int fd = open("/dev/null", O_WRONLY);
  if (fd >= 0) {
    dup2(fd, 1);
    close(fd);
  }
#ifdef __linux__
  prctl(PR_SET_PDEATHSIG, SIGKILL);
#endif
}

Term fork_workers_run(Env e, Term* f, IoWork* w) {
  u32 n = (u32)f[0];
  if (n < 2 || n > FORK_MAX) {
    return (Term)4294967295u;
  }
  fflush(stdout);
  fflush(stderr);
  pid_t pid[FORK_MAX];
  for (u32 k = 0; k < n; k += 1) {
    pid[k] = fork();
    if (pid[k] == 0) {
      fork_child_reset();
      return (Term)k;
    }
  }
  bool rej = false;
  bool dec = false;
  for (u32 k = 0; k < n; k += 1) {
    int st = 0;
    if (pid[k] < 0) {
      dec = true;
      continue;
    }
    while (waitpid(pid[k], &st, 0) < 0) {
      if (errno != EINTR) {
        st = 2 << 8;
        break;
      }
    }
    if (WIFEXITED(st) && WEXITSTATUS(st) == 1) {
      rej = true;
    } else if (!WIFEXITED(st) || WEXITSTATUS(st) != 0) {
      dec = true;
    }
  }
  if (!rej && !dec) {
    fputs("accept\n", stdout);
    fflush(stdout);
  }
  _exit(rej ? 1 : dec ? 2 : 0);
}

static void __attribute__((constructor)) fork_workers_use(void) {
  io_eff(CID(Fork.workers), fork_workers_run);
}
