// Copied from https://github.com/dafny-lang/dafny/wiki/Modeling-External-State-Correctly

module V1 {

    class {:extern} StringMap {
        ghost var content: map<string, string> 
        constructor {:extern} ()
            ensures this.content == map[]
        method {:extern} Put(key: string, value: string) 
            ensures this.content == old(this.content)[key := value]            
    }

    method Test() {
        var m := new StringMap();
        m.Put("testkey", "testvalue");
        assert "testkey" in m.content;
        assert m.content == map[];
        assert false;
    }
}




















module V2 {
    class {:extern} StringMap {
        ghost var content: map<string, string> 
        constructor {:extern} ()
            ensures this.content == map[]
        method {:extern} Put(key: string, value: string)
            modifies this
            ensures this.content == old(this.content)[key := value]            
    }

    method TestOld() {
        var m := new StringMap();
        m.Put("testkey", "testvalue");
        assert "testkey" in m.content;
        /*
        assert m.content == map[];
        assert false;
        */
    }

    method Test() {
        var m := new StringMap();
        m.content := map["never added key" := "never added value"];
        assert m.content["never added key"] == "never added value";
    }
}





















module V3 {
    class {:extern} StringMap {
        function {:extern} content(): map<string, string> 
        constructor {:extern} ()
            ensures this.content() == map[]
        method {:extern} Put(key: string, value: string)
            modifies this
            ensures this.content() == old(this.content())[key := value]            
    }

    method Test() {
        var m := new StringMap();
        m.Put("testkey", "testvalue");
        assert "testkey" in m.content();
        assert m.content() == map[];
        assert false;
    }
}


















module V4 {

    class {:extern} StringMap {
        function {:extern} content(): map<string, string> reads this
        constructor {:extern} ()
            ensures this.content() == map[]
        method {:extern} Put(key: string, value: string)
            modifies this
            ensures this.content() == old(this.content())[key := value]    
        function method {:extern} Get(key: string): (r: Result<string>)
            ensures
                match r
                case Success(value) => key in content() && content()[key] == value
                case Failure(e) => key !in content()
    }

    datatype Result<T> =
    | Success(value: T)
    | Failure(error: string)

    method Test() {
        var m := new StringMap();
        m.Put("testkey", "testvalue");
        var r := m.Get("testkey");
        assert false;
    }
}
















module V5 {
    class {:extern} StringMap {
        function {:extern} content(): map<string, string> reads this
        constructor {:extern} ()
            ensures this.content() == map[]
        method {:extern} Put(key: string, value: string)
            modifies this
            ensures this.content() == old(this.content())[key := value]    
        function method {:extern} Get(key: string): (r: Result<string>)
            reads this
            ensures
                match r
                case Success(value) => key in content() && content()[key] == value
                case Failure(e) => key !in content()
    }

    datatype Result<T> =
    | Success(value: T)
    | Failure(error: string)

    method Test() {
        var m := new StringMap();
        m.Put("testkey", "testvalue");
        var r := m.Get("testkey");
        //assert false;
    }
}


