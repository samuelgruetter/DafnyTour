// Copied from https://github.com/dafny-lang/dafny/wiki/Modeling-External-State-Correctly
// Goes with ExternalStateGood.dfy

using System;
using System.Collections.Generic;
using Lib;

namespace Externs {

    class StringMap {
        private IDictionary<String, String> content;

        public StringMap () {
            this.content = new Dictionary<String, String>();
        }

        public void Put(Dafny.Sequence<char> key, Dafny.Sequence<char> value) {
            Console.WriteLine("C# Externs.StringMap.Put is called");
            this.content.Add(key.ToString(), value.ToString());
        }

        public Result<Dafny.Sequence<char>> Get(Dafny.Sequence<char> key) {
            String result;
            if (content.TryGetValue(key.ToString(), out result)) {
                return Result<Dafny.Sequence<char>>.create_Success(
                    Dafny.Sequence<char>.FromString(result));
            } else {
                return Result<Dafny.Sequence<char>>.create_Failure(
                    Dafny.Sequence<char>.FromString("key not found"));
            }
        }
   }
}
