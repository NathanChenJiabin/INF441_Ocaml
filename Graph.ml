let graph edges =
  let vertices = List.fold_left (fun v (s,d,t) -> max v (max s t)) 0 edges + 1 in
  let g = Array.init vertices (fun _ -> Array.make vertices 0) in
  List.iter (fun (s,d,t) -> g.(s).(t) <- d) edges;
  g

let dijkstra g source =
  let pq = PriorityQueue.create () in
  let vertices = Array.length g in
  let d = Array.make vertices max_int in
  d.(source) <- 0;
  PriorityQueue.push pq 0 source;
  while not (PriorityQueue.is_empty pq) do
    let pi, i = PriorityQueue.pop pq in
    for j = 0 to vertices - 1 do
      if g.(i).(j) > 0 then
        let dj = d.(i) + g.(i).(j) in
        if dj < d.(j) then begin
          d.(j) <- dj;
          PriorityQueue.push pq dj j
        end
    done
  done;
  d

let () =
  let g =
    graph
      [
        (1,2,2);
        (1,4,3);
        (2,1,3);
        (2,4,4);
        (2,2,5);
        (3,3,5);
        (4,2,6);
        (5,3,4);
        (5,2,6);
      ]
  in
  let d = dijkstra g 1 in
  for i = 0 to Array.length g - 1 do
    Printf.printf "distance to %d : %d\n" i d.(i)
  done
