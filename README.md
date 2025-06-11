f99# N
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

/* in N we have basic while and for 
loops and for infinity(always true) 
loop -> always do 
*/

var a = 0
while(a < 3) {
    println(a) // 0, 1, 2, 3
    a += 1
}

for(i,0,3) {
    println(i) // 0, 1, 2, 3
}

// for but?

for(i,3,0) {
   println(i) // 3,2,1,0
}

always do {
    print("infinity loop")
}
```

```js
var x = input("Write num: ")
if (x < 10000) { println("small number") }
else { println("big number") }

// ternary 
var y = input("Write num from 0 to 10: ")
y < 10 ? println("Correct number") : println("Wrong number")
```

```js
// some built-in function 

// main
println(args) // write text on display, println("My name is ", name)

input(placeholder) 

factorial(num) // factorial of num

random(seed?) // random num 

// cryptography 

md5(text) // md5 hash
sha256(text) // sha256 hash

// base64

btoa(text)
atob(encoded_text)

// work with file

fread(filename) // read 
file(without print it)
fwrite(filename, text) // write text in filename 

// other

system(command) // execute 
terminal command
```


Dependencies: ply, python3 or other code runner(recommend pypy)
