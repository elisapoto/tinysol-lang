contract MutabilityTest {
    int x;

    constructor() {
        x = 0;
    }

    //Pozitive tests

    function validWrite(int val) public {
        x = val;
    }

    function validRead() public view returns (int) {
        return x;
    }

    function validPure(int a, int b) public pure returns (int) {
        return a + b;
    }

    //Negative tests

    function failViewWrite() public view {
        x = 10; 
    }

    function failPureRead() public pure returns (int) {
        return x;
    }

    function failPureWrite() public pure {
        x = 20;
    }

    function failReturn() public returns (int) {
        return true; 
    }
}