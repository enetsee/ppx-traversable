module Normal = struct
  type 'a t =
    | A of 'a 
    | B of int
    | C
  [@@deriving traversable]
end
