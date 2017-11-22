pragma solidity ^0.4.0;
contract Escrow {

    address buyer;
    address seller;
    address arbiter;
    uint256 amount;

    function Escrow(address _buyer, address _seller, uint256 _amount) public {
            require (amount > 0 && _buyer != 0 && _seller != 0);
            buyer = _buyer;
            seller = _seller;
            arbiter = msg.sender;
            amount = _amount;
    }

    function addfund() payable public  {
        require (amount > 0 && msg.value == amount && msg.sender == buyer);
        amount = 0;
    }

    function refund() public {
        require (amount == 0 && msg.sender == arbiter);
        selfdestruct(buyer);
    }

    function pay() public {
        require (amount == 0 && msg.sender == arbiter);
        selfdestruct(seller);
    }
}
