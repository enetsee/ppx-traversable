module Normal : sig
  type 'a t =
    | A of 'a
    | B of int
    | C
  [@@deriving traversable]
end
