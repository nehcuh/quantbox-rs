import toml
import os

def sort_trade_dates(file_path):
    # 读取 TOML 文件
    with open(file_path, 'r') as f:
        data = toml.load(f)
    
    # 对每个交易所的日期进行排序
    for exchange in data['trade_dates']:
        dates = data['trade_dates'][exchange]
        # 将日期转换为整数并排序
        sorted_dates = sorted([int(d) for d in dates])
        data['trade_dates'][exchange] = sorted_dates
    
    # 写回文件
    with open(file_path, 'w') as f:
        toml.dump(data, f)

if __name__ == '__main__':
    # 获取项目根目录下的 config/trade_calendar.toml 文件
    file_path = os.path.join(os.path.dirname(os.path.dirname(__file__)), 'config', 'trade_calendar.toml')
    sort_trade_dates(file_path)
    print(f"Successfully sorted trade dates in {file_path}")
