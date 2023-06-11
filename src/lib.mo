/// `Enumeration<K>` is a "set enumeration" of elements of type `K` called "keys".
///
/// A typical application is to assign permanent user numbers to princpals.
///
/// The data structure is a map `Nat -> K` with the following properties:
/// * keys are not repeated, i.e. the map is injective
/// * keys are consecutively numbered (no gaps), i.e. if n keys are stored
///   then `[0,n) -> K` is bijective
/// * keys are numbered in the order they are added to the data structure
/// * keys cannot be deleted
/// * efficient inverse lookup `K -> Nat`
/// * doubles as a set implementation (without deletion)
///
/// The data structure is optimized primarily for memory efficiency
/// and secondarily for instruction efficiency.
///
/// Copyright: 2023 MR Research AG
/// Main author: Andrii Stepanov (AStepanov25)
/// Contributors: Timo Hanke (timohanke), Yurii Pytomets (Pitometsu)

import Blob "mo:base/Blob";
import Array "mo:base/Array";
import Nat32 "mo:base/Nat32";
import Order "mo:base/Order";
import Debug "mo:base/Debug";

module {
  type Order = Order.Order;

  /// Red-black tree of key `Nat`.
  public type Tree = ?({ #R; #B }, Tree, Nat, Tree);

  public type StableEnumeration<K> = {
    var array : [var ?K];
    var size_ : Nat;
    var tree : Tree;
  };

  /// Create a stable version of the Enumeration data structure.
  /// Allows the use of the `stable` keyword to create a stable variable.
  ///
  /// Should be used in conjunction with `Enumeration.wrap_stable()`.
  ///
  /// Example:
  /// ```motoko
  ///   stable let stable_accounts = Enumeration.new_stable<Text>();
  ///   let accounts = Enumeration.wrap_stable(stable_accounts, Text.compare);
  ///
  ///   assert accounts.add("Alice") == 0;
  ///   assert accounts.get(0) == "Alice";
  ///```
  public func new_stable<K>() : StableEnumeration<K> {
    return {
      var array : [var ?K] = [var null];
      var size_ = 0;
      var tree = (null : Tree);
    };
  };

  /// Create a new bidirectional enumeration class.
  public func new_heap<K>(cmp : (K, K) -> Order) : Enumeration<K> {
    return Enumeration<K>(new_stable<K>(), cmp);
  };

  /// Wrap a stable enumeration in a class.
  /// The benefit is that the `compare` function is stored and does not need to be passed to every method.
  public func wrap_stable<K>(self : StableEnumeration<K>, cmp : (K, K) -> Order) : Enumeration<K> {
    return Enumeration<K>(self, cmp);
  };

  /// Bidirectional enumeration of any `K` s in the order they are added.
  /// For a map from `K` to index `Nat` it is implemented as red-black tree,
  /// for a map from index `Nat` to `K` the implementation is an array.
  ///
  /// Example:
  /// ```motoko
  /// let e = Enumeration.Enumeration<Blob>(Blob.compare, "");
  /// ```
  public class Enumeration<K>(self : StableEnumeration<K>, compare : (K, K) -> Order) {

    /// Add `key` to enumeration. Returns `size` if the key in new to the enumeration and index of key in enumeration otherwise.
    ///
    /// Example:
    /// ```motoko
    /// let e = Enumeration.Enumeration<Blob>(Blob.compare, "");
    /// assert(e.add("abc") == 0);
    /// assert(e.add("aaa") == 1);
    /// assert(e.add("abc") == 0);
    /// ```
    /// Runtime: O(log(n))
    public func add(key : K) : Nat {
      var index = self.size_;

      func lbalance(left : Tree, y : Nat, right : Tree) : Tree {
        switch (left, right) {
          case (?(#R, ?(#R, l1, y1, r1), y2, r2), r) ?(#R, ?(#B, l1, y1, r1), y2, ?(#B, r2, y, r));
          case (?(#R, l1, y1, ?(#R, l2, y2, r2)), r) ?(#R, ?(#B, l1, y1, l2), y2, ?(#B, r2, y, r));
          case _ ?(#B, left, y, right);
        };
      };

      func rbalance(left : Tree, y : Nat, right : Tree) : Tree {
        switch (left, right) {
          case (l, ?(#R, l1, y1, ?(#R, l2, y2, r2))) ?(#R, ?(#B, l, y, l1), y1, ?(#B, l2, y2, r2));
          case (l, ?(#R, ?(#R, l1, y1, r1), y2, r2)) ?(#R, ?(#B, l, y, l1), y1, ?(#B, r1, y2, r2));
          case _ ?(#B, left, y, right);
        };
      };

      func insert(tree : Tree) : Tree {
        switch tree {
          case (?(#B, left, y, right)) {
            switch (compare(key, get(y))) {
              case (#less) lbalance(insert(left), y, right);
              case (#greater) rbalance(left, y, insert(right));
              case (#equal) {
                index := y;
                tree;
              };
            };
          };
          case (?(#R, left, y, right)) {
            switch (compare(key, get(y))) {
              case (#less) ?(#R, insert(left), y, right);
              case (#greater) ?(#R, left, y, insert(right));
              case (#equal) {
                index := y;
                tree;
              };
            };
          };
          case (null) {
            index := self.size_;
            ?(#R, null, self.size_, null);
          };
        };
      };

      self.tree := switch (insert(self.tree)) {
        case (?(#R, left, y, right)) ?(#B, left, y, right);
        case other other;
      };

      // approximate growth by sqrt(2) by 2-powers
      // the function will trap if n == 0 or n >= 3 * 2 ** 30
      func next_size(n_ : Nat) : Nat {
        if (n_ == 1) return 2;
        let n = Nat32.fromNat(n_); // traps if n >= 2 ** 32
        let s = 30 - Nat32.bitcountLeadingZero(n); // traps if n == 0
        let m = ((n >> s) +% 1) << s;
        assert (m != 0); // traps if n >= 3 * 2 ** 30
        Nat32.toNat(m);
      };

      if (index == self.size_) {
        if (self.size_ == self.array.size()) {
          self.array := Array.tabulateVar<?K>(next_size(self.size_), func(i) = if (i < self.size_) { self.array[i] } else { null });
        };
        self.array[self.size_] := ?key;
        self.size_ += 1;
      };

      index;
    };

    /// Returns `?index` where `index` is the index of `key` in order it was added to enumeration, or `null` it `key` wasn't added.
    ///
    /// Example:
    /// ```motoko
    /// let e = Enumeration.Enumeration<Blob>(Blob.compare, "");
    /// assert(e.add("abc") == 0);
    /// assert(e.add("aaa") == 1);
    /// assert(e.lookup("abc") == ?0);
    /// assert(e.lookup("aaa") == ?1);
    /// assert(e.lookup("bbb") == null);
    /// ```
    /// Runtime: O(log(n))
    public func lookup(key : K) : ?Nat {
      func get_in_tree(x : K, t : Tree) : ?Nat {
        switch t {
          case (?(_, l, y, r)) {
            switch (compare(x, get(y))) {
              case (#less) get_in_tree(x, l);
              case (#equal) ?y;
              case (#greater) get_in_tree(x, r);
            };
          };
          case (null) null;
        };
      };

      get_in_tree(key, self.tree);
    };

    /// Returns `K` with index `index`. Traps it index is out of bounds.
    ///
    /// Example:
    /// ```motoko
    /// let e = Enumeration.Enumeration<Blob>(Blob.compare, "");
    /// assert(e.add("abc") == 0);
    /// assert(e.add("aaa") == 1);
    /// assert(e.get(0) == "abc");
    /// assert(e.get(1) == "aaa");
    /// ```
    /// Runtime: O(1)
    public func get(index : Nat) : K {
      switch (self.array[index]) {
        case (null) Debug.trap("Enumeration: index out of bounds");
        case (?key) key;
      };
    };

    /// Returns number of unique keys added to enumeration.
    ///
    /// Example:
    /// ```motoko
    /// let e = Enumeration.Enumeration<Blob>(Blob.compare, "");
    /// assert(e.add("abc") == 0);
    /// assert(e.add("aaa") == 1);
    /// assert(e.size() == 2);
    /// ```
    /// Runtime: O(1)
    public func size() : Nat = self.size_;

    /// Returns pair of red-black self. for map from `K` to `Nat` and
    /// array of `K` for map from `Nat` to `K`.
    ///
    /// Example:
    /// ```motoko
    /// let e = Enumeration.Enumeration<Blob>(Blob.compare, "");
    /// assert(e.add("abc") == 0);
    /// assert(e.add("aaa") == 1);
    /// e.unsafeUnshare(e.share()); // Nothing changed
    /// ```
    /// Runtime: O(1)
    public func share() : (Tree, [var ?K], Nat) = (self.tree, self.array, self.size_);

    /// Sets self content from red-black tree for map from `K` to `Nat`
    /// and array of `K` for map from `Nat` to `K`.
    /// `t` should be a valid red-black tree and correspond to array `a`.
    /// This function does not perform any validation.
    ///
    /// Example:
    /// ```motoko
    /// let e = Enumeration.Enumeration<Blob>(Blob.compare, "");
    /// assert(e.add("abc") == 0);
    /// assert(e.add("aaa") == 1);
    /// e.unsafeUnshare(e.share()); // Nothing changed
    /// ```
    /// Runtime: O(1)
    public func unsafeUnshare(data : (Tree, [var ?K], Nat)) {
      self.tree := data.0;
      self.array := data.1;
      self.size_ := data.2;
    };
  };
};
