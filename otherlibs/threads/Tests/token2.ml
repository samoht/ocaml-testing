(* Performance test for I/O scheduling *)

let mut = Mutex.create()

let niter = ref 0

let token = ref 0

let process (n, ins, outs, nprocs) =
  let buf = String.create 1 in
  while true do
    ThreadUnix.read ins.(n) buf 0 1;
    (* Printf.printf "Thread %d got the token\n" n; *)
    if n = 0 then begin
      decr niter;
      if !niter <= 0 then exit 0
    end;
    let next = if n + 1 >= nprocs then 0 else n + 1 in
    (* Printf.printf "Thread %d sending token to thread %d\n" n next; *)
    ThreadUnix.write outs.(next) buf 0 1
  done

let main() =
  let nprocs = int_of_string Sys.argv.(1) in
  let iter = int_of_string Sys.argv.(2) in
  let ins = Array.create nprocs Unix.stdin in
  let outs = Array.create nprocs Unix.stdout in
  for n = 0 to nprocs - 1 do
    let (i, o) = ThreadUnix.pipe() in ins.(n) <- i; outs.(n) <- o
  done;
  niter := iter;
  for i = 0 to nprocs - 1 do Thread.create process (i, ins, outs, nprocs) done;
  ThreadUnix.write outs.(0) "X" 0 1;
  Thread.delay 3600.

let _ = main()
