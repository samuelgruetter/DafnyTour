// Copied from https://github.com/dafny-lang/dafny/wiki/Modeling-External-State-Correctly

module {:extern "Lib"} Lib {
    datatype Result<T> =
    | Success(value: T)
    | Failure(error: string)
}

module {:extern "Externs"} Externs {
    import opened Lib

    class {:extern} StringMap {
        function {:extern} content(): map<string, string>
            // If I forget the reads clause here, I will get
            // "insufficient reads clause to read field"
            // in the implementation in Externs_Feasability
            reads this

        constructor {:extern} ()
            ensures this.content() == map[]

        method {:extern} Put(key: string, value: string)
            // If I forget the modifies clause here, I will get
            // "assignment may update an object not in the enclosing context's
            // modifies clause" in the implementation in Externs_Feasability
            modifies this
            ensures this.content() == old(this.content())[key := value]    

        function method {:extern} Get(key: string): (r: Result<string>)
            // If I forget the reads clause here, I will get
            // "insufficient reads clause to read field"
            // in the implementation in Externs_Feasability
            reads this
            ensures
                match r
                case Success(value) => 
                    key in content() && content()[key] == value
                case Failure(e) =>
                    key !in content()
    }
}

module Externs_Feasability refines Externs {
    class StringMap {
        var private_content: map<string, string>
        function content(): map<string, string> { private_content }

        function method Get(key: string): (r: Result<string>) {
            if key in private_content 
            then Success(private_content[key]) 
            else Failure("key not found")
        }

        method Put(key: string, value: string) {
            print "Externs_Feasability.StringMap.Put is called\n";
            this.private_content := this.private_content[key := value];
        }
    }
}

module Program {
    // uncomment import below if you want to check that all methods
    // have a feasability check (need to compile to C# to detect missing ones)
    //import opened Externs_Feasability
    import opened Externs

    method Main() {
        var m := new StringMap();
        m.Put("testkey", "testvalue");
        assert m.content()["testkey"] == "testvalue";
        var v := m.Get("testkey").value;
        assert v == "testvalue";
        print v, "\n";
    }
}

// dafny ExternalStateGood.dfy ExternalStateStringMap.cs /compile:3
