// Fork.workers(n) under JavaScript: no fork (4294967295), so this process
// is the only worker.
function fork_workers(n) {
  return 4294967295;
}

io_eff(CID(Fork.workers), fork_workers);
