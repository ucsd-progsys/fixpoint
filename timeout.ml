

module M = Mutex
module T = Thread

let get_time () = int_of_float (Unix.time ())

let do_timeout i f x =
  let g x lk (ret, rd) =
    let rv = f x in
    M.lock lk; ret := Some rv; rd := true; M.unlock lk in
  let (ret, rd) as rr = (ref None, ref false) in
  let stime = get_time () in
  let lk = M.create () in 
  let t  = T.create (g x lk) rr in
  while (M.lock lk; let trd = !rd in (M.unlock lk; not(trd))) do
    if (get_time () - stime < i) then
      T.yield ()
    else
      (T.kill t; ret := None; rd := true)
  done; !ret


