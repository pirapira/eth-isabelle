pragma solidity ^0.4.0;
contract EscrowWallet {

    address from;
    address to;
    address owner;
    uint256 amount;

    function EscrowWallet(address _from, address _to, uint256 _amount) public {
            require (amount > 0);
            from = _from;
            to = _to;
            owner = msg.sender;
            amount = _amount;
    }

    function addfund() payable public  {
        require (amount > 0 && msg.value == amount && msg.sender == from);
        amount = 0;
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
