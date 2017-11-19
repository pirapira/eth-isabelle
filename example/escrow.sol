pragma solidity ^0.4.0;
contract EscrowWallet {

    address from;
    address to;
    address owner;

    function EscrowWallet(address _from, address _to) public {
            from = _from;
            to = _to;
            owner = msg.sender;
    }

    function addfund() payable public  {
        require (msg.value > 0 && msg.sender == from);
    }

    function refund() public {
        require (msg.sender == owner);
        selfdestruct(from);
    }

    function pay() public {
        require (msg.sender == owner);
        selfdestruct(to);
    }
}
