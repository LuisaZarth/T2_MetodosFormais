class DequeCircular {
  // Atributos concretos e framing
  var arr: array<int>
  var head: int
  var count: int
  ghost var Repr: set<object>

  // Representação abstrata
  ghost var Conteudo: seq<int>

  // Invariante de consistência da classe
  ghost predicate Valid()
    reads this, Repr
  {
    this in Repr &&
    arr in Repr &&
    arr.Length > 0 &&
    0 <= head < arr.Length &&
    0 <= count <= arr.Length &&
    |Conteudo| == count &&
    (forall i :: 0 <= i < count ==> 
        Conteudo[i] == arr[(head + i) % arr.Length])
  }

  // Construtor
  constructor(capacidade: int)
    requires capacidade > 0
    ensures Valid()
    ensures fresh(Repr)
    ensures count == 0
    ensures arr.Length == capacidade
    ensures Conteudo == []
  {
    arr := new int[capacidade];
    head := 0;
    count := 0;
    Conteudo := [];
    Repr := {this, arr};
  }

  // Operações de consulta básica
  function Tamanho(): (tam: int)
    requires Valid()
    reads Repr
    ensures tam == count
    ensures tam == |Conteudo|
  {
    count
  }

  function Capacidade(): (cap: int)
    requires Valid()
    reads Repr
    ensures cap == arr.Length
    ensures cap > 0
  {
    arr.Length
  }
}

//Verifica se o deque está cheio
method EstaCheio() returns (cheio: bool)
  requires Valid()
  ensures Valid()
  ensures cheio == (count == arr.Length)
{
  cheio := count == arr.Length;
}

//Adiciona um elemento ao final do deque
method AdicionarFinal(valor: int)
  requires Valid()
  requires count < arr.Length
  modifies Repr
  ensures Valid()
  ensures count == old(count) + 1
  ensures Conteudo == old(Conteudo) + [valor]
{
  var pos := (head + count) % arr.Length;

  arr[pos] := valor;
  Conteudo := Conteudo + [valor];
  count := count + 1;
}

//Adiciona um elemento ao inicio do deque
method AdicionarInicio(valor: int)
  requires Valid()
  requires count < arr.Length
  modifies Repr
  ensures Valid()
  ensures count == old(count) + 1
  ensures Conteudo == [valor] + old(Conteudo)
{
  var novoHead := (head - 1 + arr.Length) % arr.Length;

  arr[novoHead] := valor;
  head := novoHead;
  Conteudo := [valor] + Conteudo;
  count := count + 1;
}
}
