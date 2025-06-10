# N
Powerful language for everything

# Examples

```js
// assign
var x = 1
var y = 1.5
var z = x + y
```

```js
// function definition 
func add(a, b) {
    return a + b
}

println(add(2,2)) // 4

// lambda function definition 
var a = lambda (a, b) { return a+b }

println(a(3,4)) // 7
```

```js
// loops

/* in N we have basic while and for loops and for infinity(always true) loop -> always do 
*/

var a = 0
while(a < 3) {
    println(a) // 0, 1, 2, 3
    a += 1
}

for(i,0,3) {
    println(i) // 0, 1, 2, 3
}

always do {
    print("infinity loop")
}
```

Dependencies: ply, python3 or other code runner(recommend pypy)
