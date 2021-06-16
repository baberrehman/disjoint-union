### Tags and type-directed elimination and Question 2)

There are two different aspects that can be used to classify union types:

1) Are tags needed to build expressions in the language with union types?

2) Is some extra information present at runtime (a tag or type) to help
indentifying the origin of the value?

We are talking about tagged vs untagged in the sense of 1). Our source
expressions do not need tags to build expressions that have union types.
We illustrate this with examples in Section 2. For instance:


```
function safediv ( x : Int ) ( y : Int ) : String | Int =
  if ( y == 0) then inj1 " Divided by zero " else inj2 ( x / y )

```

```safediv``` returns either String or Int and exlicit tags are used for each
value of String (inj1) and Int (inj2).
With tagged union types, programmer has to explicitly mention the
tag (inj1 and inj2 in this example) to create an expression of a
tagged union type.

Similarly, tags are used in the elimination of tagged unions:

```
function tostring ( x : String | Int ) : String = switch ( x )
					inj1 str -> str
					inj2 num -> show num
```

Switch construct in ```tostring``` decides which branch to choose based upon the tag.
We assume that show is a function which returns string representation of expressions
of any type as in Haskell.

Whereas, in untagged setting of union types, programmer doesn't has to
explicitly mention the tag, as in exmaple below:

```
String | Integer safediv3 ( Integer x , Integer y ) {
	if ( y ==0) { return " Divided by zero " ; }
	else        { return ( x / y ) ; }
}
```

```safediv3``` returns either String or Integer, but without using explicit tags.
It is to be noted that ```safediv3``` simply returns a value, without
mentioning inj1 or inj2 as in safediv.

Elimination in untagged union types is also without explicit tags:

```
String tostring2 ( String | Integer x ) {
	switch ( x )
		case ( is String  )	{ return x ) ; }
		case ( is Integer ) { return str(x) ) ; }
}
```

Function ```tostring2``` dynamically checks the type of x and selects
respective case branch to execute. It is noted that switch
construct in ```tostring2``` does not use explicit tags as in ```tostring```.

Our work follows the later approach (untagged unions) in which
tags are not required to construct and eliminate expressions
of union types. However, some information is required to check
the type of switch expression at runtime. This information comes
from the notion of dynamic types in our system. Programmer does
not explicitly has to mention tags, for example a switch expression
in our system is written as:

```
switch ( val ) {
	( x : Int )    -> x*2 ,
	( y : String ) -> y
}
```

We refer to section 2 (line 417) for detailed discussion.